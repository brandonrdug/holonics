import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Tactic

/-!
# BrendleHungHinge: the corrected second-variation expansion

This file isolates the exact algebra in the second-order hinge of the Brendle--Hung
preprint.  It does not construct a metric or assert a curvature identity.

The source has a linear term and two quadratic contributions,

`P₀ L h² + P₀ Q(h¹,h¹) + 1/2 r(h¹) · z(h¹)`.

The ten-component expansion is lawful only after the `Q` term and the `r-z`
contraction have both been made symmetric.  Those are separate typed hypotheses
below.  With them, the mixed `c-d` coefficient is forced to be
`2 * λc * λd * Vcd`; it cannot be replaced by another `2 * λd * Vdd` term.
-/

noncomputable section

namespace Soma.Holonics.Millennium.BrendleHungHinge

/-- Algebraic data used by the second-variation calculation.  The fields name only
linearity and the two symmetries actually required by the displayed expansion. -/
structure SecondVariationData
    (R H Z : Type*) [Field R] [CharZero R] [AddCommGroup H] [Module R H]
    [AddCommGroup Z] [Module R Z] where
  linear : H →ₗ[R] R
  quadratic : H →ₗ[R] H →ₗ[R] R
  quadratic_symm : ∀ x y, quadratic x y = quadratic y x
  r : H →ₗ[R] Z
  z : H →ₗ[R] Z
  contract : Z →ₗ[R] Z →ₗ[R] R
  rz_symm : ∀ x y, contract (r x) (z y) = contract (r y) (z x)

variable {R H Z : Type*} [Field R] [CharZero R] [AddCommGroup H] [Module R H]
  [AddCommGroup Z] [Module R Z]

/-- The combined symmetric bilinear term occurring in the source formula. -/
def SecondVariationData.pairing (D : SecondVariationData R H Z) (x y : H) : R :=
  D.quadratic x y + (2 : R)⁻¹ * D.contract (D.r x) (D.z y)

theorem SecondVariationData.pairing_symm (D : SecondVariationData R H Z) (x y : H) :
    D.pairing x y = D.pairing y x := by
  simp only [SecondVariationData.pairing, D.quadratic_symm x y, D.rz_symm x y]

theorem SecondVariationData.pairing_add_left
    (D : SecondVariationData R H Z) (x y w : H) :
    D.pairing (x + y) w = D.pairing x w + D.pairing y w := by
  simp only [SecondVariationData.pairing, map_add, LinearMap.add_apply]
  ring

theorem SecondVariationData.pairing_add_right
    (D : SecondVariationData R H Z) (x y w : H) :
    D.pairing x (y + w) = D.pairing x y + D.pairing x w := by
  simp only [SecondVariationData.pairing, map_add]
  ring

theorem SecondVariationData.pairing_smul_left
    (D : SecondVariationData R H Z) (a : R) (x y : H) :
    D.pairing (a • x) y = a * D.pairing x y := by
  simp only [SecondVariationData.pairing, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem SecondVariationData.pairing_smul_right
    (D : SecondVariationData R H Z) (a : R) (x y : H) :
    D.pairing x (a • y) = a * D.pairing x y := by
  simp only [SecondVariationData.pairing, map_smul, smul_eq_mul]
  ring

/-- The source's second-variation scalar, stripped of all geometric interpretation. -/
def secondVariation (D : SecondVariationData R H Z) (h₁ h₂ : H) : R :=
  D.linear h₂ + D.pairing h₁ h₁

/-- One diagonal or mixed component.  In particular, `Vcd` uses `h₂cd`, not
`h₂bd`. -/
def variationComponent (D : SecondVariationData R H Z)
    (h₁i h₁j h₂ij : H) : R :=
  D.linear h₂ij + D.pairing h₁i h₁j

/-- The first-order perturbation from the source. -/
def firstPerturbation (lamC lamD : R) (ha hb hc hd : H) : H :=
  ha + hb + lamC • hc + lamD • hd

/-- The corrected second-order perturbation from the source. -/
def secondPerturbation (lamC lamD : R)
    (haa hbb hab hcc hac hbc hdd had hbd hcd : H) : H :=
  haa + hbb + (2 : R) • hab + lamC ^ 2 • hcc +
    (2 * lamC) • hac + (2 * lamC) • hbc + lamD ^ 2 • hdd +
    (2 * lamD) • had + (2 * lamD) • hbd + (2 * lamC * lamD) • hcd

/-- **THE CORRECT SYMMETRIC BILINEAR EXPANSION.**

The last summand is forced to be `2 * λc * λd * Vcd`.  Since `Vcd` is constructed
with `h₂cd`, both source transcription defects are excluded by the theorem's type. -/
theorem theSecondVariationHasTheCorrectTenComponentExpansion
    (D : SecondVariationData R H Z) (lamC lamD : R)
    (ha hb hc hd haa hbb hab hcc hac hbc hdd had hbd hcd : H) :
    secondVariation D
        (firstPerturbation lamC lamD ha hb hc hd)
        (secondPerturbation lamC lamD haa hbb hab hcc hac hbc hdd had hbd hcd)
      = variationComponent D ha ha haa
        + variationComponent D hb hb hbb
        + 2 * variationComponent D ha hb hab
        + lamC ^ 2 * variationComponent D hc hc hcc
        + 2 * lamC * variationComponent D ha hc hac
        + 2 * lamC * variationComponent D hb hc hbc
        + lamD ^ 2 * variationComponent D hd hd hdd
        + 2 * lamD * variationComponent D ha hd had
        + 2 * lamD * variationComponent D hb hd hbd
        + 2 * lamC * lamD * variationComponent D hc hd hcd := by
  simp only [secondVariation, firstPerturbation, secondPerturbation,
    variationComponent, map_add, map_smul,
    SecondVariationData.pairing_add_left, SecondVariationData.pairing_add_right,
    SecondVariationData.pairing_smul_left, SecondVariationData.pairing_smul_right,
    smul_eq_mul]
  rw [D.pairing_symm hb ha, D.pairing_symm hc ha,
    D.pairing_symm hc hb, D.pairing_symm hd ha,
    D.pairing_symm hd hb, D.pairing_symm hd hc]
  ring

/-- A one-dimensional exact model used to separate the `cd` component from the
`dd` component. -/
def transcriptionWitness : SecondVariationData ℚ ℚ ℚ where
  linear := LinearMap.id
  quadratic := 0
  quadratic_symm := by simp
  r := 0
  z := 0
  contract := 0
  rz_symm := by simp

/-- **THE REPEATED-`Vdd` TRANSCRIPTION IS NOT A BILINEAR IDENTITY.**
Already in a one-dimensional linear model, the correct `2*λc*λd*Vcd` term is
nonzero while the repeated `2*λd*Vdd` term is zero. -/
theorem theRepeatedVddTermCannotReplaceTheCdTerm :
    (2 : ℚ) * 1 * 1 * variationComponent transcriptionWitness 0 0 1 ≠
      (2 : ℚ) * 1 * variationComponent transcriptionWitness 0 0 0 := by
  norm_num [variationComponent, SecondVariationData.pairing, transcriptionWitness]

/-! ## The actual `ac`/`bc` source coefficients -/

/-- Scalar coefficient multiplying the symmetrized `K_ex K_ez` tensor in
`h²_ac`, as printed in the source archive. -/
def acMixedCoefficient (θ q1z : ℝ) : ℝ :=
  (1 / 10 : ℝ) * Real.cos θ * q1z *
    (-5 - 14 * Real.cos (2 * θ) + 3 * Real.cos (4 * θ))

/-- Scalar coefficient multiplying the symmetrized `K_ey K_ez` tensor in
`h²_bc`, as printed in the source archive. -/
def bcMixedCoefficient (θ q2z : ℝ) : ℝ :=
  (1 / 10 : ℝ) * Real.sin θ * q2z *
    (-5 + 14 * Real.cos (2 * θ) + 3 * Real.cos (4 * θ))

/-- **THE PRINTED `bc` COEFFICIENT IS THE EXCHANGE OF THE PRINTED `ac` COEFFICIENT.**
The exchange is `θ ↦ π/2 - θ`, together with the external frame exchange
`q1z ↦ q2z` and `ex ↦ ey`.  This checks the scalar part of the actual source
formula; the frame and curvature-operator equivariance remain separate obligations. -/
theorem theBcCoefficientIsTheAcCoefficientUnderExchange (θ qz : ℝ) :
    bcMixedCoefficient θ qz = acMixedCoefficient (Real.pi / 2 - θ) qz := by
  unfold bcMixedCoefficient acMixedCoefficient
  rw [Real.cos_pi_div_two_sub,
    show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring,
    Real.cos_pi_sub,
    show 4 * (Real.pi / 2 - θ) = 2 * Real.pi - 4 * θ by ring,
    Real.cos_two_pi_sub]
  ring

/-! ## The exact remaining route to `Vbc = 0` -/

/-- **EXCHANGE EQUIVARIANCE TRANSPORTS THE CHECKED `Vac` IDENTITY TO `Vbc`.**
This is deliberately conditional: it names the exact frame/operator symmetry that
must still be checked from the geometric formulas. -/
theorem vbc_vanishes_from_exactExchangeEquivariance
    (D : SecondVariationData R H Z) (σ : H ≃ₗ[R] H)
    (ha hb hc hac hbc : H)
    (hσa : σ ha = hb) (hσc : σ hc = hc) (hσac : σ hac = hbc)
    (hlinear : ∀ x, D.linear (σ x) = D.linear x)
    (hpairing : ∀ x y, D.pairing (σ x) (σ y) = D.pairing x y)
    (hVac : variationComponent D ha hc hac = 0) :
    variationComponent D hb hc hbc = 0 := by
  rw [← hσa, ← hσc, ← hσac]
  unfold variationComponent
  rw [hlinear, hpairing]
  exact hVac

/-! ## The corrected `λd` smallness orientation -/

/-- The squared-error absorption condition is equivalent to the corrected threshold
`|λd| ≤ sqrt (δ / C)` when `C > 0`.  This rules out the reversed `sqrt (C / δ)`
orientation independently of any curvature claim. -/
theorem lambdaSmallness_iff_correctSquareRootBound
    {δ C lamD : ℝ} (hδ : 0 ≤ δ) (hC : 0 < C) :
    lamD ^ 2 * C ≤ δ ↔ |lamD| ≤ Real.sqrt (δ / C) := by
  have hratio : 0 ≤ δ / C := div_nonneg hδ hC.le
  have hsqrt : 0 ≤ Real.sqrt (δ / C) := Real.sqrt_nonneg _
  constructor
  · intro h
    have hsquare : lamD ^ 2 ≤ δ / C := (le_div_iff₀ hC).2 h
    apply (sq_le_sq₀ (abs_nonneg lamD) hsqrt).mp
    simpa [Real.sq_sqrt hratio] using hsquare
  · intro h
    apply (le_div_iff₀ hC).1
    have hsquare := (sq_le_sq₀ (abs_nonneg lamD) hsqrt).2 h
    simpa [Real.sq_sqrt hratio] using hsquare

end Soma.Holonics.Millennium.BrendleHungHinge
