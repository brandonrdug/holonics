import ElementaryHolonics.Millennium.FamilyThetaWaldspurgerBridge
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Tunnell half-integral theta carrier

This file constructs the object on the arithmetic side of the missing
Waldspurger--Tunnell passage.  It has two exact receivers founded by the same two
positive ternary quadratic forms:

* an analytic receiver on the upper half-plane, assembled from Jacobi theta
  functions;
* a formal `q`-expansion receiver whose coefficients are the complete finite
  representation populations already constructed in
  `FamilyThetaWaldspurgerBridge`.

The two forms are

`Q_thin(x,y,z) = 2x² + y² + 8z²`,

`Q_thick(x,y,z) = 2x² + y² + 32z²`.

The difference `2 Θ_thick - Θ_thin` is the exact odd-index receiver whose `n`-th
odd coefficient is `2 A_n - B_n`.  The complete level-128 carrier additionally
retains the level-four correction forced by `Θ(τ) - Θ(4τ)`.  This removes the
previously prose-only half-integral theta carrier without confusing its odd receiver
with its global modular source.  Petersson normalization and the Waldspurger
period-square law remain later constitutive passages; they are not fields of this
construction.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellThetaCarrier

open Complex
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyWaldspurgerGate

/-! ## 1. The common quadratic source -/

/-- The addressed integral population underlying both theta receivers. -/
abbrev TernaryOccurrence := ℤ × ℤ × ℤ

/-- The thin positive ternary quadratic form. -/
def thinQuadraticForm (t : TernaryOccurrence) : ℤ :=
  2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2

/-- The thick positive ternary quadratic form. -/
def thickQuadraticForm (t : TernaryOccurrence) : ℤ :=
  2 * t.1 ^ 2 + t.2.1 ^ 2 + 32 * t.2.2 ^ 2

/-- The level-four thin correction form. -/
def levelThinQuadraticForm (t : TernaryOccurrence) : ℤ :=
  4 * t.1 ^ 2 + 2 * t.2.1 ^ 2 + 8 * t.2.2 ^ 2

/-- The level-four thick correction form. -/
def levelThickQuadraticForm (t : TernaryOccurrence) : ℤ :=
  4 * t.1 ^ 2 + 2 * t.2.1 ^ 2 + 32 * t.2.2 ^ 2

theorem thinQuadraticForm_nonneg (t : TernaryOccurrence) :
    0 ≤ thinQuadraticForm t := by
  unfold thinQuadraticForm
  positivity

theorem thickQuadraticForm_nonneg (t : TernaryOccurrence) :
    0 ≤ thickQuadraticForm t := by
  unfold thickQuadraticForm
  positivity

/-! ## 2. The analytic upper-half-plane receiver -/

/-- `Θ(aτ) = Σ_m exp(2πi a m²τ)`, expressed in mathlib's convention
`jacobiTheta σ = Σ_m exp(πi m²σ)` by the exact rebase `σ = 2aτ`. -/
def scaledUnaryTheta (a : ℕ) (τ : ℂ) : ℂ :=
  jacobiTheta ((2 * a : ℂ) * τ)

/-- The analytic theta series of `Q_thin`. -/
def thinAnalyticTheta (τ : ℂ) : ℂ :=
  scaledUnaryTheta 2 τ * scaledUnaryTheta 1 τ * scaledUnaryTheta 8 τ

/-- The analytic theta series of `Q_thick`. -/
def thickAnalyticTheta (τ : ℂ) : ℂ :=
  scaledUnaryTheta 2 τ * scaledUnaryTheta 1 τ * scaledUnaryTheta 32 τ

/-- The analytic receiver sufficient on odd coefficients. -/
def oddCoefficientAnalyticTheta (τ : ℂ) : ℂ :=
  2 * thickAnalyticTheta τ - thinAnalyticTheta τ

/-- Tunnell's complete level-128 half-integral theta carrier in integral
normalization: `2 (Θ(τ)-Θ(4τ)) Θ(2τ) (Θ(32τ)-Θ(8τ)/2)`. -/
def tunnellAnalyticTheta (τ : ℂ) : ℂ :=
  (scaledUnaryTheta 1 τ - scaledUnaryTheta 4 τ) * scaledUnaryTheta 2 τ *
    (2 * scaledUnaryTheta 32 τ - scaledUnaryTheta 8 τ)

private theorem jacobiTheta_period_two : Function.Periodic jacobiTheta (2 : ℂ) := by
  intro τ
  simpa [add_comm] using jacobiTheta_two_add τ

/-- Every scaled unary theta returns after one turn in the base parameter. -/
theorem scaledUnaryTheta_add_one (a : ℕ) (τ : ℂ) :
    scaledUnaryTheta a (τ + 1) = scaledUnaryTheta a τ := by
  unfold scaledUnaryTheta
  rw [show (2 * a : ℂ) * (τ + 1) =
      (2 * a : ℂ) * τ + a • (2 : ℂ) by
    simp only [nsmul_eq_mul]
    ring]
  exact (jacobiTheta_period_two.nsmul a) ((2 * a : ℂ) * τ)

/-- The oriented analytic carrier returns after the unit translation. -/
theorem tunnellAnalyticTheta_add_one (τ : ℂ) :
    tunnellAnalyticTheta (τ + 1) = tunnellAnalyticTheta τ := by
  simp only [tunnellAnalyticTheta, scaledUnaryTheta_add_one]

/-- Each positive-scale unary theta is holomorphic at every point of the upper
half-plane. -/
theorem differentiableAt_scaledUnaryTheta {a : ℕ} (ha : 0 < a)
    {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (scaledUnaryTheta a) τ := by
  unfold scaledUnaryTheta
  have him : 0 < (((2 * a : ℂ) * τ).im) := by
    rw [mul_im]
    norm_num
    positivity
  exact (differentiableAt_jacobiTheta him).comp τ (by fun_prop)

/-- The Tunnell analytic carrier is holomorphic on the upper half-plane. -/
theorem differentiableAt_tunnellAnalyticTheta {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ tunnellAnalyticTheta τ := by
  unfold tunnellAnalyticTheta
  have h1 := differentiableAt_scaledUnaryTheta (a := 1) (by norm_num) hτ
  have h2 := differentiableAt_scaledUnaryTheta (a := 2) (by norm_num) hτ
  have h4 := differentiableAt_scaledUnaryTheta (a := 4) (by norm_num) hτ
  have h8 := differentiableAt_scaledUnaryTheta (a := 8) (by norm_num) hτ
  have h32 := differentiableAt_scaledUnaryTheta (a := 32) (by norm_num) hτ
  exact ((h1.sub h4).mul h2).mul
    (((differentiableAt_const (c := (2 : ℂ))).mul h32).sub h8)

/-! ## 3. The exact formal coefficient receiver -/

/-- The thin ternary theta `q`-expansion. -/
def thinThetaQExpansion : PowerSeries ℤ :=
  PowerSeries.mk thinThetaCoefficient

/-- The thick ternary theta `q`-expansion. -/
def thickThetaQExpansion : PowerSeries ℤ :=
  PowerSeries.mk thickThetaCoefficient

/-- The complete level-four thin correction population. -/
def levelThinPopulation (n : ℕ) : Finset TernaryOccurrence :=
  ((LatticeCount.boxZ (Nat.sqrt n)) ×ˢ
      (LatticeCount.boxZ (Nat.sqrt n)) ×ˢ
      (LatticeCount.boxZ (Nat.sqrt n))).filter
    fun t => levelThinQuadraticForm t = (n : ℤ)

/-- The complete level-four thick correction population. -/
def levelThickPopulation (n : ℕ) : Finset TernaryOccurrence :=
  ((LatticeCount.boxZ (Nat.sqrt n)) ×ˢ
      (LatticeCount.boxZ (Nat.sqrt n)) ×ˢ
      (LatticeCount.boxZ (Nat.sqrt n))).filter
    fun t => levelThickQuadraticForm t = (n : ℤ)

def levelThinCoefficient (n : ℕ) : ℤ := (levelThinPopulation n).card

def levelThickCoefficient (n : ℕ) : ℤ := (levelThickPopulation n).card

def levelThinThetaQExpansion : PowerSeries ℤ :=
  PowerSeries.mk levelThinCoefficient

def levelThickThetaQExpansion : PowerSeries ℤ :=
  PowerSeries.mk levelThickCoefficient

/-- The complete integral coefficient of Tunnell's level-128 form. -/
def fullTunnellThetaCoefficient (n : ℕ) : ℤ :=
  tunnellThetaCoefficient n - 2 * levelThickCoefficient n + levelThinCoefficient n

/-- The old two-form receiver, sufficient and exact on every odd coefficient. -/
def oddTunnellThetaQExpansion : PowerSeries ℤ :=
  PowerSeries.mk tunnellThetaCoefficient

/-- The complete oriented integral `q`-expansion. -/
def tunnellThetaQExpansion : PowerSeries ℤ :=
  PowerSeries.mk fullTunnellThetaCoefficient

@[simp] theorem coeff_thinThetaQExpansion (n : ℕ) :
    PowerSeries.coeff n thinThetaQExpansion = thinThetaCoefficient n := by
  simp [thinThetaQExpansion]

@[simp] theorem coeff_thickThetaQExpansion (n : ℕ) :
    PowerSeries.coeff n thickThetaQExpansion = thickThetaCoefficient n := by
  simp [thickThetaQExpansion]

@[simp] theorem coeff_tunnellThetaQExpansion (n : ℕ) :
    PowerSeries.coeff n tunnellThetaQExpansion = fullTunnellThetaCoefficient n := by
  simp [tunnellThetaQExpansion]

@[simp] theorem coeff_oddTunnellThetaQExpansion (n : ℕ) :
    PowerSeries.coeff n oddTunnellThetaQExpansion = tunnellThetaCoefficient n := by
  simp [oddTunnellThetaQExpansion]

/-- The thin coefficient is the cardinality of the complete, addressed source fibre
of the thin quadratic receiver. -/
theorem coeff_thinThetaQExpansion_eq_sourceFibre_card (n : ℕ) :
    PowerSeries.coeff n thinThetaQExpansion =
      ((canonicalThinPopulation n).card : ℤ) := by
  simp [thinThetaCoefficient]

/-- The thick coefficient is the cardinality of the complete, addressed source fibre
of the thick quadratic receiver. -/
theorem coeff_thickThetaQExpansion_eq_sourceFibre_card (n : ℕ) :
    PowerSeries.coeff n thickThetaQExpansion =
      ((canonicalThickPopulation n).card : ℤ) := by
  simp [thickThetaCoefficient]

/-- Membership in the thin coefficient fibre is exactly incidence with the thin
quadratic form, together with the proved-sufficient finite aperture. -/
theorem mem_thinCoefficientSourceFibre_iff (n : ℕ) (t : TernaryOccurrence) :
    t ∈ canonicalThinPopulation n ↔
      (t.1 ∈ LatticeCount.boxZ (Nat.sqrt n) ∧
        t.2.1 ∈ LatticeCount.boxZ (Nat.sqrt n) ∧
        t.2.2 ∈ LatticeCount.boxZ (Nat.sqrt n)) ∧
      thinQuadraticForm t = (n : ℤ) := by
  simp [canonicalThinPopulation, LatticeCount.SolFr, thinQuadraticForm]

/-- Membership in the thick coefficient fibre is the corresponding exact thick-form
incidence. -/
theorem mem_thickCoefficientSourceFibre_iff (n : ℕ) (t : TernaryOccurrence) :
    t ∈ canonicalThickPopulation n ↔
      (t.1 ∈ LatticeCount.boxZ (Nat.sqrt n) ∧
        t.2.1 ∈ LatticeCount.boxZ (Nat.sqrt n) ∧
        t.2.2 ∈ LatticeCount.boxZ (Nat.sqrt n)) ∧
      thickQuadraticForm t = (n : ℤ) := by
  simpa [thickQuadraticForm] using mem_canonicalThickPopulation_iff n t

/-- The level-four correction has no odd thin coefficient because every represented
integer is even. -/
theorem levelThinPopulation_eq_empty_of_odd {n : ℕ} (hn : Odd n) :
    levelThinPopulation n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [levelThinPopulation, Finset.mem_filter] at ht
  rcases hn with ⟨k, hk⟩
  unfold levelThinQuadraticForm at ht
  omega

/-- The same parity exclusion for the thick level correction. -/
theorem levelThickPopulation_eq_empty_of_odd {n : ℕ} (hn : Odd n) :
    levelThickPopulation n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [levelThickPopulation, Finset.mem_filter] at ht
  rcases hn with ⟨k, hk⟩
  unfold levelThickQuadraticForm at ht
  omega

/-- Consequently the complete level-128 coefficient and the earlier two-form
receiver agree at every odd index. -/
theorem fullTunnellThetaCoefficient_eq_tunnellThetaCoefficient_of_odd
    {n : ℕ} (hn : Odd n) :
    fullTunnellThetaCoefficient n = tunnellThetaCoefficient n := by
  rw [fullTunnellThetaCoefficient, levelThinCoefficient, levelThickCoefficient,
    levelThinPopulation_eq_empty_of_odd hn, levelThickPopulation_eq_empty_of_odd hn]
  simp

/-- The global formal carrier is literally the oriented difference of the two
ternary theta series, not merely coefficientwise at a selected prime. -/
theorem oddTunnellThetaQExpansion_eq_two_mul_thick_sub_thin :
    oddTunnellThetaQExpansion =
      PowerSeries.C (2 : ℤ) * thickThetaQExpansion - thinThetaQExpansion := by
  ext n
  rw [coeff_oddTunnellThetaQExpansion, map_sub, PowerSeries.coeff_C_mul,
    coeff_thickThetaQExpansion, coeff_thinThetaQExpansion]
  rfl

/-- The complete formal level-128 carrier is the old odd receiver plus the exact
level-four correction. -/
theorem tunnellThetaQExpansion_eq_level_corrected :
    tunnellThetaQExpansion =
      oddTunnellThetaQExpansion -
        PowerSeries.C (2 : ℤ) * levelThickThetaQExpansion +
        levelThinThetaQExpansion := by
  ext n
  rw [coeff_tunnellThetaQExpansion, map_add, map_sub, PowerSeries.coeff_C_mul,
    coeff_oddTunnellThetaQExpansion]
  simp only [levelThickThetaQExpansion, levelThinThetaQExpansion,
    PowerSeries.coeff_mk]
  rfl

/-- The coefficient receiver lands on the already constructed canonical branch
count, including its orbit normalization by four. -/
theorem canonicalBranchCount_eq_tunnellQCoefficient_div_four
    {n : ℕ} (hn : Odd n) :
    canonicalBranchCount n =
      PowerSeries.coeff n tunnellThetaQExpansion / 4 := by
  rw [coeff_tunnellThetaQExpansion,
    fullTunnellThetaCoefficient_eq_tunnellThetaCoefficient_of_odd hn,
    canonicalBranchCount_eq_tunnellThetaCoefficient_div_four]

/-- On the BSD branch the actual coefficient is four times an odd integer, hence
is nonzero without an estimate. -/
theorem tunnellQCoefficient_ne_zero {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 3) :
    PowerSeries.coeff p tunnellThetaQExpansion ≠ 0 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [coeff_tunnellThetaQExpansion,
    fullTunnellThetaCoefficient_eq_tunnellThetaCoefficient_of_odd hpodd,
    ← canonicalSignedTernaryCount_eq_tunnellThetaCoefficient,
    canonicalSignedTernaryCount_eq_four_mul_count hp8]
  apply mul_ne_zero (by norm_num)
  intro hzero
  obtain ⟨k, hk⟩ := canonicalBranchCount_odd hp8
  omega

/-! ## 4. One constructed carrier, two receivers -/

/-- The completed source-specific carrier.  Its laws are theorem fields proved by
the constructions above; it contains no Waldspurger or BSD hypothesis. -/
structure TunnellThetaCarrier where
  analytic : ℂ → ℂ
  qExpansion : PowerSeries ℤ
  analytic_eq : analytic = tunnellAnalyticTheta
  qExpansion_eq : qExpansion = tunnellThetaQExpansion
  translationReturn : Function.Periodic analytic 1
  holomorphicOnUpperHalfPlane : ∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ analytic τ
  coefficientReturn : ∀ n : ℕ,
    PowerSeries.coeff n qExpansion = fullTunnellThetaCoefficient n

/-- The Tunnell theta carrier is inhabited by the actual analytic product and exact
formal series constructed in this file. -/
def theTunnellThetaCarrier : TunnellThetaCarrier where
  analytic := tunnellAnalyticTheta
  qExpansion := tunnellThetaQExpansion
  analytic_eq := rfl
  qExpansion_eq := rfl
  translationReturn := tunnellAnalyticTheta_add_one
  holomorphicOnUpperHalfPlane := fun _ hτ => differentiableAt_tunnellAnalyticTheta hτ
  coefficientReturn := coeff_tunnellThetaQExpansion

#print axioms tunnellAnalyticTheta_add_one
#print axioms differentiableAt_tunnellAnalyticTheta
#print axioms oddTunnellThetaQExpansion_eq_two_mul_thick_sub_thin
#print axioms mem_thinCoefficientSourceFibre_iff
#print axioms canonicalBranchCount_eq_tunnellQCoefficient_div_four
#print axioms tunnellQCoefficient_ne_zero
#print axioms theTunnellThetaCarrier

end Soma.Holonics.Millennium.FamilyTunnellThetaCarrier
