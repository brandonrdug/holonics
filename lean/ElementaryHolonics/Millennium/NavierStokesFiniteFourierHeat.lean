import ElementaryHolonics.Millennium.NavierStokesFourierTriads

/-!
# Finite Fourier heat transport on the three-torus

This module owns the exact diagonal heat transport on a declared finite set of integer
frequencies.  The multiplier at `k` is

`exp (-nu * t * (2 * pi)^2 * |k|^2)`.

On divergence-free finite states this is also the finite Stokes transport: the scalar diagonal
action preserves the existing Fourier divergence constraint.  The carrier stays finite
throughout.  No infinite Fourier series, Galerkin-limit convergence, nonlinear
Navier--Stokes solution, or continuation consequence is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFourierTriads

/-- [definition] A finite Fourier state retains one complex three-vector at every addressed mode
in the declared finite carrier. -/
abbrev FiniteFourierState (carrier : Finset SpatialFrequency) :=
  (k : {k // k ∈ carrier}) → ComplexVector

/-- [definition] The nonnegative diagonal eigenvalue of `-Δ` on the unit three-torus at frequency
`k`. -/
def torusStokesEigenvalue (k : SpatialFrequency) : ℝ :=
  (2 * Real.pi) ^ 2 * frequencySquared k

/-- [proved-derived] Every diagonal Stokes eigenvalue is nonnegative. -/
theorem torusStokesEigenvalue_nonneg (k : SpatialFrequency) :
    0 ≤ torusStokesEigenvalue k := by
  apply mul_nonneg (sq_nonneg (2 * Real.pi))
  unfold frequencySquared
  exact Finset.sum_nonneg fun j _hj ↦ sq_nonneg (k j : ℝ)

/-- [proved-derived] Every nonzero frequency has a strictly positive Stokes eigenvalue. -/
theorem torusStokesEigenvalue_pos {k : SpatialFrequency} (hk : k ≠ 0) :
    0 < torusStokesEigenvalue k := by
  apply mul_pos
  · positivity
  · exact frequencySquared_pos hk

/-- [definition] Exact heat/Stokes multiplier for viscosity `nu`, elapsed time `t`, and mode
`k`. -/
def heatStokesMultiplier (nu t : ℝ) (k : SpatialFrequency) : ℝ :=
  Real.exp (-(nu * t * torusStokesEigenvalue k))

@[simp]
theorem heatStokesMultiplier_zero_time (nu : ℝ) (k : SpatialFrequency) :
    heatStokesMultiplier nu 0 k = 1 := by
  simp [heatStokesMultiplier]

@[simp]
theorem heatStokesMultiplier_zero_frequency (nu t : ℝ) :
    heatStokesMultiplier nu t 0 = 1 := by
  simp [heatStokesMultiplier, torusStokesEigenvalue, frequencySquared]

/-- [proved-derived] Diagonal heat multipliers compose exactly under addition of elapsed times. -/
theorem heatStokesMultiplier_add
    (nu s t : ℝ) (k : SpatialFrequency) :
    heatStokesMultiplier nu (s + t) k =
      heatStokesMultiplier nu s k * heatStokesMultiplier nu t k := by
  rw [heatStokesMultiplier, heatStokesMultiplier, heatStokesMultiplier]
  rw [show -(nu * (s + t) * torusStokesEigenvalue k) =
      (-(nu * s * torusStokesEigenvalue k)) +
        (-(nu * t * torusStokesEigenvalue k)) by ring]
  exact Real.exp_add _ _

/-- [definition] The exact finite diagonal heat action.  The scalar action is coordinatewise on
the complex velocity mode and never changes the finite carrier. -/
def finiteHeatStokesEvolution
    {carrier : Finset SpatialFrequency} (nu t : ℝ)
    (state : FiniteFourierState carrier) : FiniteFourierState carrier :=
  fun k ↦ (heatStokesMultiplier nu t k.1 : ℂ) • state k

@[simp]
theorem finiteHeatStokesEvolution_apply
    {carrier : Finset SpatialFrequency} (nu t : ℝ)
    (state : FiniteFourierState carrier) (k : {k // k ∈ carrier}) :
    finiteHeatStokesEvolution nu t state k =
      (heatStokesMultiplier nu t k.1 : ℂ) • state k := rfl

/-- [proved-derived] Zero elapsed time is the identity on every finite carrier. -/
@[simp]
theorem finiteHeatStokesEvolution_zero_time
    {carrier : Finset SpatialFrequency} (nu : ℝ)
    (state : FiniteFourierState carrier) :
    finiteHeatStokesEvolution nu 0 state = state := by
  funext k
  simp [finiteHeatStokesEvolution]

/-- [proved-derived] The finite diagonal heat action is an exact semigroup. -/
theorem finiteHeatStokesEvolution_add
    {carrier : Finset SpatialFrequency} (nu s t : ℝ)
    (state : FiniteFourierState carrier) :
    finiteHeatStokesEvolution nu (s + t) state =
      finiteHeatStokesEvolution nu s (finiteHeatStokesEvolution nu t state) := by
  funext k
  rw [finiteHeatStokesEvolution_apply, finiteHeatStokesEvolution_apply,
    finiteHeatStokesEvolution_apply, heatStokesMultiplier_add]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- [definition] Modewise incompressibility on the finite carrier, using the genuine-torus
frequency embedding supplied by `NavierStokesTorusFourier`. -/
def IsFiniteDivergenceFree
    {carrier : Finset SpatialFrequency} (state : FiniteFourierState carrier) : Prop :=
  ∀ k, complexDot (complexFrequencyVector k.1) (state k) = 0

/-- [proved-derived] The diagonal heat action preserves every finite Fourier divergence
constraint, so its restriction to `IsFiniteDivergenceFree` is the finite Stokes action. -/
theorem finiteHeatStokesEvolution_preserves_divergenceFree
    {carrier : Finset SpatialFrequency} {state : FiniteFourierState carrier}
    (hstate : IsFiniteDivergenceFree state) (nu t : ℝ) :
    IsFiniteDivergenceFree (finiteHeatStokesEvolution nu t state) := by
  intro k
  simp only [finiteHeatStokesEvolution_apply, complexDot, dotProduct_smul, smul_eq_mul]
  change (heatStokesMultiplier nu t k.1 : ℂ) *
      complexDot (complexFrequencyVector k.1) (state k) = 0
  rw [hstate k, mul_zero]

/-- [definition] The finite squared-amplitude energy receiver, summed over every retained mode
and all three complex velocity coordinates. -/
def finiteFourierEnergy
    {carrier : Finset SpatialFrequency} (state : FiniteFourierState carrier) : ℝ :=
  ∑ k : {k // k ∈ carrier}, ∑ j : Fin 3, Complex.normSq (state k j)

/-- [proved-derived] For nonnegative viscosity and elapsed time, every diagonal multiplier lies
in the closed unit interval. -/
theorem heatStokesMultiplier_mem_unitInterval
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) (k : SpatialFrequency) :
    heatStokesMultiplier nu t k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hnu ht)
      (torusStokesEigenvalue_nonneg k))

/-- [proved-derived] Exact finite energy formula after one diagonal heat/Stokes passage. -/
theorem finiteFourierEnergy_evolution_eq
    {carrier : Finset SpatialFrequency} (state : FiniteFourierState carrier)
    (nu t : ℝ) :
    finiteFourierEnergy (finiteHeatStokesEvolution nu t state) =
      ∑ k : {k // k ∈ carrier},
        (heatStokesMultiplier nu t k.1) ^ 2 *
          ∑ j : Fin 3, Complex.normSq (state k j) := by
  unfold finiteFourierEnergy
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [finiteHeatStokesEvolution_apply, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, pow_two]

/-- [proved-derived] Nonnegative viscosity makes the finite heat/Stokes passage energy
nonexpanding at every nonnegative elapsed time. -/
theorem finiteFourierEnergy_evolution_le
    {carrier : Finset SpatialFrequency} (state : FiniteFourierState carrier)
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    finiteFourierEnergy (finiteHeatStokesEvolution nu t state) ≤
      finiteFourierEnergy state := by
  unfold finiteFourierEnergy
  apply Finset.sum_le_sum
  intro k _hk
  apply Finset.sum_le_sum
  intro j _hj
  simp only [finiteHeatStokesEvolution_apply, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  obtain ⟨hm0, hm1⟩ := heatStokesMultiplier_mem_unitInterval hnu ht k.1
  have hsquare :
      heatStokesMultiplier nu t k.1 * heatStokesMultiplier nu t k.1 ≤ 1 := by
    nlinarith
  exact mul_le_of_le_one_left (Complex.normSq_nonneg _) hsquare

/-- [proved-derived] The energy lost to a nonnegative finite viscous passage is nonnegative. -/
theorem finiteViscousEnergyLoss_nonneg
    {carrier : Finset SpatialFrequency} (state : FiniteFourierState carrier)
    {nu t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    0 ≤ finiteFourierEnergy state -
      finiteFourierEnergy (finiteHeatStokesEvolution nu t state) := by
  exact sub_nonneg.mpr (finiteFourierEnergy_evolution_le state hnu ht)

#print axioms torusStokesEigenvalue_nonneg
#print axioms torusStokesEigenvalue_pos
#print axioms heatStokesMultiplier_add
#print axioms finiteHeatStokesEvolution_add
#print axioms finiteHeatStokesEvolution_preserves_divergenceFree
#print axioms finiteFourierEnergy_evolution_eq
#print axioms finiteFourierEnergy_evolution_le
#print axioms finiteViscousEnergyLoss_nonneg

end Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
