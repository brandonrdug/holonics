import ElementaryHolonics.Millennium.NavierStokesFrozenSharpSourceBoundary
import ElementaryHolonics.Millennium.NavierStokesOpenEnergySpacetime
import ElementaryHolonics.Millennium.NavierStokesScaling

/-!
# The energy-owned critical square face and its first shell separator

**[proved-derived; formal-checked]**  The three-dimensional energy endpoints carry one exact
instantaneous scale-critical product: the `L2` velocity face has weight `-1/2`, the `H1`
dissipation face has weight `1/2`, and their product has weight zero.  This is also the weight of
vorticity in homogeneous order `-1/2` (equivalently velocity in order `1/2`).  It is therefore
the strongest scale-critical Hilbert/square receiver naturally suggested by the already-owned
open-lifespan energy current.

The frozen source boundary retains enough cancellation to act before absolute coefficient mass,
but the standing terminal receiver subsequently asks for an `l1` frequency population.  The
exact cubic-shell construction below identifies the first unpaid passage.  At dyadic radius `R`,
there are exactly `R^3` separately addressed occurrences in one translated lattice cube.  The
critical negative-half square coordinate is `R^-1 * sum |a_k|^2`.  Cauchy--Schwarz therefore
costs `R^2` when reconstructing `sum |a_k|`; the constant unit section attains that cost exactly.
No scale-independent factorization through this energy square receiver exists.

This is an exact receiver separator, not a blow-up construction and not terminal control.  It
does not identify a Hilbert square with the complete phase-bearing coefficient section: the latter
is retained as the reconstruction fibre.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.NavierStokesCriticalEnergySquareSeparator

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesScaling

/-! ## The exact critical weight carried by the energy endpoints -/

/-- Weight of the instantaneous product of the kinetic `L2` norm and the velocity-gradient
`L2` norm.  The two factors remain distinct receiver faces. -/
def energyEndpointSquareProductWeight (dimension : ℚ) : ℚ :=
  energyWeight dimension + enstrophyWeight dimension

/-- Vorticity has one more spatial derivative than velocity. -/
def vorticitySobolevWeight (dimension order : ℚ) : ℚ :=
  2 + order - dimension / 2

/-- In dimension three, the energy endpoint product and the negative-half vorticity square face
are both exactly scale critical. -/
theorem energyEndpointSquareProduct_and_negativeHalfVorticity_are_critical :
    energyEndpointSquareProductWeight 3 = 0 ∧
      vorticitySobolevWeight 3 (-1 / 2) = 0 ∧
      vorticitySobolevWeight 3 (-1 / 2) = sobolevWeight 3 (1 / 2) := by
  norm_num [energyEndpointSquareProductWeight, energyWeight, enstrophyWeight,
    vorticitySobolevWeight, sobolevWeight]

/-- After the frozen resolvent recovers one spatial derivative, the strongest square face paid by
the energy source has vorticity order `1/2`.  Its target-time integral still has weight `-1`, not
the weight-zero terminal vorticity integral. -/
def integratedEnergyPaidFrozenSquareWeight : ℚ :=
  vorticitySobolevWeight 3 (1 / 2) - 2

theorem integratedEnergyPaidFrozenSquare_is_energyWeighted_not_terminalCritical :
    integratedEnergyPaidFrozenSquareWeight = -1 ∧
      integratedEnergyPaidFrozenSquareWeight ≠ 0 := by
  norm_num [integratedEnergyPaidFrozenSquareWeight, vorticitySobolevWeight]

/-! ## One exact three-dimensional dyadic shell population -/

/-- The receiver radius of the shell addressed by `level`. -/
def criticalEnergyShellRadius (level : ℕ) : ℕ := 2 ^ level

theorem criticalEnergyShellRadius_pos (level : ℕ) :
    0 < criticalEnergyShellRadius level := by
  simp [criticalEnergyShellRadius]

/-- A translated cubic lattice block of side `R` inside one dyadic annulus has three independent
frequency coordinates and therefore `R^3` separately addressed occurrences. -/
abbrev CriticalEnergyShellOccurrence (level : ℕ) :=
  Fin (criticalEnergyShellRadius level) ×
    Fin (criticalEnergyShellRadius level) ×
      Fin (criticalEnergyShellRadius level)

theorem card_criticalEnergyShellOccurrence (level : ℕ) :
    Fintype.card (CriticalEnergyShellOccurrence level) =
      criticalEnergyShellRadius level ^ 3 := by
  simp [CriticalEnergyShellOccurrence]
  ring

/-- The occurrence address embeds into the actual three-dimensional lattice as the translated
cube `[R,2R)^3`, hence inside one dyadic frequency annulus. -/
def criticalEnergyShellFrequency
    (level : ℕ) (occurrence : CriticalEnergyShellOccurrence level) :
    SpatialFrequency := fun coordinate ↦
  if coordinate = 0 then
    Int.ofNat (criticalEnergyShellRadius level + occurrence.1.1)
  else if coordinate = 1 then
    Int.ofNat (criticalEnergyShellRadius level + occurrence.2.1.1)
  else
    Int.ofNat (criticalEnergyShellRadius level + occurrence.2.2.1)

theorem criticalEnergyShellFrequency_coordinate_bounds
    (level : ℕ) (occurrence : CriticalEnergyShellOccurrence level)
    (coordinate : Fin 3) :
    (criticalEnergyShellRadius level : ℤ) ≤
        criticalEnergyShellFrequency level occurrence coordinate ∧
      criticalEnergyShellFrequency level occurrence coordinate <
        2 * (criticalEnergyShellRadius level : ℤ) := by
  fin_cases coordinate <;>
    simp [criticalEnergyShellFrequency] <;>
    omega

/-- Distinct shell occurrences remain distinct lattice frequencies; the `R^3` population is not
a multiplicity artifact. -/
theorem criticalEnergyShellFrequency_injective (level : ℕ) :
    Function.Injective (criticalEnergyShellFrequency level) := by
  rintro ⟨firstX, firstY, firstZ⟩ ⟨secondX, secondY, secondZ⟩ hfrequency
  apply Prod.ext
  · apply Fin.ext
    have hcoordinate := congrFun hfrequency (0 : Fin 3)
    simp [criticalEnergyShellFrequency] at hcoordinate
    omega
  · apply Prod.ext
    · apply Fin.ext
      have hcoordinate := congrFun hfrequency (1 : Fin 3)
      simp [criticalEnergyShellFrequency] at hcoordinate
      omega
    · apply Fin.ext
      have hcoordinate := congrFun hfrequency (2 : Fin 3)
      simp [criticalEnergyShellFrequency] at hcoordinate
      omega

/-- The complete complex coefficient section on one addressed cubic shell.  Relative phase and
every occurrence remain present here; the two scalar receivers below are later quotients. -/
abbrev CriticalEnergyShellSection (level : ℕ) :=
  CriticalEnergyShellOccurrence level → ℂ

/-- Absolute coefficient mass requested by the current terminal Fourier receiver. -/
def criticalEnergyShellAbsoluteMass
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  ∑ occurrence, ‖carrier occurrence‖

/-- Shell coordinate of the critical negative-half Hilbert receiver.  The weight `R^-1` is kept
as a distinct scale incidence rather than absorbed into the coefficient population. -/
def criticalEnergyShellSquareMass
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  (criticalEnergyShellRadius level : ℝ)⁻¹ *
    ∑ occurrence, ‖carrier occurrence‖ ^ 2

/-- Norm coordinate of the same nonnegative square receiver. -/
def criticalEnergyShellSquareNorm
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  Real.sqrt (criticalEnergyShellSquareMass carrier)

theorem criticalEnergyShellSquareMass_nonneg
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    0 ≤ criticalEnergyShellSquareMass carrier := by
  unfold criticalEnergyShellSquareMass
  positivity

/-! ## The exact shell conversion and its sharp firing section -/

/-- Cauchy--Schwarz identifies the precise shell price of forgetting the complete complex
section and retaining only its critical square coordinate. -/
theorem criticalEnergyShellAbsoluteMass_sq_le_radius_four_mul_squareMass
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    criticalEnergyShellAbsoluteMass carrier ^ 2 ≤
      (criticalEnergyShellRadius level : ℝ) ^ 4 *
        criticalEnergyShellSquareMass carrier := by
  let radius : ℝ := criticalEnergyShellRadius level
  have hradius : 0 < radius := by
    change 0 < (criticalEnergyShellRadius level : ℝ)
    exact_mod_cast criticalEnergyShellRadius_pos level
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (CriticalEnergyShellOccurrence level))
    (fun occurrence ↦ ‖carrier occurrence‖) (fun _ ↦ (1 : ℝ))
  have hcard :
      ((Fintype.card (CriticalEnergyShellOccurrence level) : ℕ) : ℝ) =
        radius ^ 3 := by
    simp [radius]
    ring
  have hones :
      (∑ _occurrence : CriticalEnergyShellOccurrence level, (1 : ℝ) ^ 2) =
        radius ^ 3 := by
    simpa only [one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using hcard
  calc
    criticalEnergyShellAbsoluteMass carrier ^ 2 =
        (∑ occurrence, ‖carrier occurrence‖ * (1 : ℝ)) ^ 2 := by
      simp [criticalEnergyShellAbsoluteMass]
    _ ≤
        (∑ occurrence, ‖carrier occurrence‖ ^ 2) *
          ∑ _occurrence : CriticalEnergyShellOccurrence level, (1 : ℝ) ^ 2 := hcs
    _ =
        (∑ occurrence, ‖carrier occurrence‖ ^ 2) * radius ^ 3 := by
      rw [hones]
    _ = radius ^ 4 * criticalEnergyShellSquareMass carrier := by
      unfold criticalEnergyShellSquareMass
      dsimp only [radius]
      field_simp [hradius.ne']

/-- The constant unit coefficient section supplies the firing family. -/
def unitCriticalEnergyShellSection (level : ℕ) :
    CriticalEnergyShellSection level := fun _ ↦ 1

theorem unitCriticalEnergyShellSection_absoluteMass (level : ℕ) :
    criticalEnergyShellAbsoluteMass (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 3 := by
  simp [criticalEnergyShellAbsoluteMass, unitCriticalEnergyShellSection]
  ring

theorem unitCriticalEnergyShellSection_squareMass (level : ℕ) :
    criticalEnergyShellSquareMass (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 2 := by
  have hradius : (criticalEnergyShellRadius level : ℝ) ≠ 0 := by
    exact_mod_cast (criticalEnergyShellRadius_pos level).ne'
  simp [criticalEnergyShellSquareMass, unitCriticalEnergyShellSection]
  field_simp

theorem unitCriticalEnergyShellSection_squareNorm (level : ℕ) :
    criticalEnergyShellSquareNorm (unitCriticalEnergyShellSection level) =
      criticalEnergyShellRadius level := by
  rw [criticalEnergyShellSquareNorm,
    unitCriticalEnergyShellSection_squareMass, Real.sqrt_sq_eq_abs,
    abs_of_pos (by
      exact_mod_cast criticalEnergyShellRadius_pos level :
        (0 : ℝ) < criticalEnergyShellRadius level)]

/-- The unit section attains the full `R^2` conversion price. -/
theorem unitCriticalEnergyShellSection_sharp_ratio (level : ℕ) :
    criticalEnergyShellAbsoluteMass (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 2 *
        criticalEnergyShellSquareNorm (unitCriticalEnergyShellSection level) := by
  rw [unitCriticalEnergyShellSection_absoluteMass,
    unitCriticalEnergyShellSection_squareNorm]
  norm_cast

/-! ## The stronger square face after the frozen boundary recovers one derivative -/

/-- The shell coordinate of vorticity `H^(1/2)`: this is one full derivative stronger than the
critical negative-half square receiver and is the strongest spatial square face suggested by the
energy-class nonlinear source after the inverse-Stokes/curl boundary action. -/
def energyPaidFrozenShellSquareMass
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  (criticalEnergyShellRadius level : ℝ) *
    ∑ occurrence, ‖carrier occurrence‖ ^ 2

def energyPaidFrozenShellSquareNorm
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  Real.sqrt (energyPaidFrozenShellSquareMass carrier)

theorem energyPaidFrozenShellSquareMass_nonneg
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    0 ≤ energyPaidFrozenShellSquareMass carrier := by
  unfold energyPaidFrozenShellSquareMass
  positivity

/-- The recovered-derivative square face is exactly `R^2` times the critical negative-half face;
this is a typed scale passage, not an identification of the two receivers. -/
theorem energyPaidFrozenShellSquareMass_eq_radius_sq_mul_critical
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    energyPaidFrozenShellSquareMass carrier =
      (criticalEnergyShellRadius level : ℝ) ^ 2 *
        criticalEnergyShellSquareMass carrier := by
  have hradius : (criticalEnergyShellRadius level : ℝ) ≠ 0 := by
    exact_mod_cast (criticalEnergyShellRadius_pos level).ne'
  unfold energyPaidFrozenShellSquareMass criticalEnergyShellSquareMass
  field_simp

/-- Even after retaining the full derivative recovered by the frozen boundary, absolute mass
costs one uncancelled power of the shell radius. -/
theorem criticalEnergyShellAbsoluteMass_sq_le_radius_sq_mul_energyPaidFrozenSquareMass
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    criticalEnergyShellAbsoluteMass carrier ^ 2 ≤
      (criticalEnergyShellRadius level : ℝ) ^ 2 *
        energyPaidFrozenShellSquareMass carrier := by
  rw [energyPaidFrozenShellSquareMass_eq_radius_sq_mul_critical]
  calc
    criticalEnergyShellAbsoluteMass carrier ^ 2 ≤
        (criticalEnergyShellRadius level : ℝ) ^ 4 *
          criticalEnergyShellSquareMass carrier :=
      criticalEnergyShellAbsoluteMass_sq_le_radius_four_mul_squareMass carrier
    _ = (criticalEnergyShellRadius level : ℝ) ^ 2 *
        ((criticalEnergyShellRadius level : ℝ) ^ 2 *
          criticalEnergyShellSquareMass carrier) := by ring

theorem unitCriticalEnergyShellSection_energyPaidFrozenSquareMass (level : ℕ) :
    energyPaidFrozenShellSquareMass (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 4 := by
  rw [energyPaidFrozenShellSquareMass_eq_radius_sq_mul_critical,
    unitCriticalEnergyShellSection_squareMass]
  ring

theorem unitCriticalEnergyShellSection_energyPaidFrozenSquareNorm (level : ℕ) :
    energyPaidFrozenShellSquareNorm (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 2 := by
  rw [energyPaidFrozenShellSquareNorm,
    unitCriticalEnergyShellSection_energyPaidFrozenSquareMass,
    show (criticalEnergyShellRadius level : ℝ) ^ 4 =
      ((criticalEnergyShellRadius level : ℝ) ^ 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sq_nonneg (criticalEnergyShellRadius level : ℝ))]

/-- The unit shell attains the remaining linear shell price exactly. -/
theorem unitCriticalEnergyShellSection_energyPaidFrozenSharpRatio (level : ℕ) :
    criticalEnergyShellAbsoluteMass (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) *
        energyPaidFrozenShellSquareNorm (unitCriticalEnergyShellSection level) := by
  rw [unitCriticalEnergyShellSection_absoluteMass,
    unitCriticalEnergyShellSection_energyPaidFrozenSquareNorm]
  ring

/-- This is the first impossible summation on the strongest energy-paid frozen square route:
one uncancelled shell radius remains, so no scale-independent coefficient reaches `l1`. -/
theorem exists_shell_separating_energyPaidFrozenSquareNorm_from_absoluteMass
    (coefficient : ℝ) :
    ∃ level : ℕ,
      coefficient *
          energyPaidFrozenShellSquareNorm (unitCriticalEnergyShellSection level) <
        criticalEnergyShellAbsoluteMass (unitCriticalEnergyShellSection level) := by
  have hpow : Tendsto (fun level : ℕ ↦ (2 : ℝ) ^ level) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨level, hlevel⟩ := (hpow.eventually_gt_atTop coefficient).exists
  refine ⟨level, ?_⟩
  rw [unitCriticalEnergyShellSection_energyPaidFrozenSquareNorm,
    unitCriticalEnergyShellSection_absoluteMass]
  have hradius : 0 < (criticalEnergyShellRadius level : ℝ) := by
    exact_mod_cast criticalEnergyShellRadius_pos level
  have hcoefficient : coefficient < (criticalEnergyShellRadius level : ℝ) := by
    simpa [criticalEnergyShellRadius] using hlevel
  nlinarith [sq_pos_of_pos hradius]

theorem no_uniform_absoluteMass_factorization_through_energyPaidFrozenSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalEnergyShellAbsoluteMass carrier ≤
        coefficient * energyPaidFrozenShellSquareNorm carrier := by
  rintro ⟨coefficient, hcoefficient⟩
  obtain ⟨level, hseparate⟩ :=
    exists_shell_separating_energyPaidFrozenSquareNorm_from_absoluteMass coefficient
  exact (not_lt_of_ge
    (hcoefficient level (unitCriticalEnergyShellSection level))) hseparate

/-- Every proposed scale-independent coefficient is defeated by one exact dyadic shell. -/
theorem exists_shell_separating_squareNorm_from_absoluteMass (coefficient : ℝ) :
    ∃ level : ℕ,
      coefficient *
          criticalEnergyShellSquareNorm (unitCriticalEnergyShellSection level) <
        criticalEnergyShellAbsoluteMass (unitCriticalEnergyShellSection level) := by
  have hpow : Tendsto (fun level : ℕ ↦ (2 : ℝ) ^ level) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨level, hlevel⟩ := (hpow.eventually_gt_atTop coefficient).exists
  refine ⟨level, ?_⟩
  rw [unitCriticalEnergyShellSection_squareNorm,
    unitCriticalEnergyShellSection_absoluteMass]
  have hradius : 0 < (criticalEnergyShellRadius level : ℝ) := by
    exact_mod_cast criticalEnergyShellRadius_pos level
  have hradiusOne : 1 ≤ (criticalEnergyShellRadius level : ℝ) := by
    exact_mod_cast (criticalEnergyShellRadius_pos level)
  have hcoefficient : coefficient < (criticalEnergyShellRadius level : ℝ) := by
    simpa [criticalEnergyShellRadius] using hlevel
  have hcoefficientSq : coefficient <
      (criticalEnergyShellRadius level : ℝ) ^ 2 := by
    exact hcoefficient.trans_le (by nlinarith)
  nlinarith [mul_pos hradius hradius]

/-- Therefore the complete absolute coefficient population does not factor uniformly through
the energy-owned critical square receiver.  The missing object must add a scale-local summability
law (or an equivalent cancellation-sensitive receiver), not merely another Hilbert estimate. -/
theorem no_uniform_absoluteMass_factorization_through_energyCriticalSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalEnergyShellAbsoluteMass carrier ≤
        coefficient * criticalEnergyShellSquareNorm carrier := by
  rintro ⟨coefficient, hcoefficient⟩
  obtain ⟨level, hseparate⟩ :=
    exists_shell_separating_squareNorm_from_absoluteMass coefficient
  exact (not_lt_of_ge
    (hcoefficient level (unitCriticalEnergyShellSection level))) hseparate

section Audit

#print axioms energyEndpointSquareProduct_and_negativeHalfVorticity_are_critical
#print axioms integratedEnergyPaidFrozenSquare_is_energyWeighted_not_terminalCritical
#print axioms card_criticalEnergyShellOccurrence
#print axioms criticalEnergyShellFrequency_coordinate_bounds
#print axioms criticalEnergyShellFrequency_injective
#print axioms criticalEnergyShellAbsoluteMass_sq_le_radius_four_mul_squareMass
#print axioms unitCriticalEnergyShellSection_absoluteMass
#print axioms unitCriticalEnergyShellSection_squareMass
#print axioms unitCriticalEnergyShellSection_squareNorm
#print axioms unitCriticalEnergyShellSection_sharp_ratio
#print axioms energyPaidFrozenShellSquareMass_eq_radius_sq_mul_critical
#print axioms criticalEnergyShellAbsoluteMass_sq_le_radius_sq_mul_energyPaidFrozenSquareMass
#print axioms unitCriticalEnergyShellSection_energyPaidFrozenSquareMass
#print axioms unitCriticalEnergyShellSection_energyPaidFrozenSquareNorm
#print axioms unitCriticalEnergyShellSection_energyPaidFrozenSharpRatio
#print axioms exists_shell_separating_energyPaidFrozenSquareNorm_from_absoluteMass
#print axioms no_uniform_absoluteMass_factorization_through_energyPaidFrozenSquare
#print axioms exists_shell_separating_squareNorm_from_absoluteMass
#print axioms no_uniform_absoluteMass_factorization_through_energyCriticalSquare

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalEnergySquareSeparator
