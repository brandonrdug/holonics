import ElementaryHolonics.Millennium.NavierStokesAlignedStrainBudget
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionFullStrain
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction

/-!
# The exterior face of the aligned strain is a circle multiplier times an integer generator

The aligned strain differential at a point splits, at any frequency-cube radius `N`, into an
exterior face carried by the modes inside the cube and an interior face carried by the
complementary coefficient tail.  This owner pays the exterior face exactly:

```text
|exterior_N(q)| ≤ 2π · G(N) · ‖u(t)‖_{L²,3} · L¹(ω(q))²,     G(N) = Σ_{k ∈ cube N} |k|₁,
```

where `2π` is the derivative multiplier of the unit-torus character, `G(N)` is the exact integer
generator of the cube face (`G(N) = 3 (2N+1)² N (N+1)`), and the componentwise `L²` receiver is
bounded by `3√(2E)` with `E` the periodic kinetic energy, itself nonincreasing.  No coordinate
comparison power `3^k` enters the exterior constant; the only constants are the circle multiplier,
the lattice face count, and the half-density `√2` of the kinetic energy.

The interior face is Sol's coefficient tail mass over the complement of the cube.  It carries the
whole terminal obligation; nothing here bounds it.

**Chart remark.**  In the cube chart the face is an integer generator.  Read in the Euclidean
sphere chart the same face is a lattice-point count whose leading term carries the solid angle
`4π`, so the transition between the two charts couples `π` to the integer factors exactly as
`Ellipse.theEightPiFactors` couples the Einstein coupling `8π = 2·(4π)` to the half-density and the
solid angle.  That transition is stated here as prose; only the cube chart is proved.
-/

noncomputable section

open Set Filter Topology
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesExteriorFaceGenerator

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget

/-! ## The exterior face generator -/

/-- [definition] The exact integer generator of the cube face: the total coordinate `ℓ¹` length of
the modes inside the frequency cube of radius `N`.  Its closed form is `3 (2N+1)² N (N+1)`. -/
def exteriorFaceMass (radius : ℕ) : ℝ :=
  ∑ k ∈ frequencyCube radius, frequencyL1 k

theorem exteriorFaceMass_nonneg (radius : ℕ) : 0 ≤ exteriorFaceMass radius :=
  Finset.sum_nonneg fun k _ => frequencyL1_nonneg k

/-! ## One derivative mode costs the circle multiplier times its coordinate length -/

theorem abs_coordinate_le_frequencyL1 (k : SpatialFrequency) (coordinate : Fin 3) :
    |(k coordinate : ℝ)| ≤ frequencyL1 k := by
  unfold frequencyL1
  fin_cases coordinate <;> simp <;>
    linarith [abs_nonneg ((k 0 : ℝ)), abs_nonneg ((k 1 : ℝ)), abs_nonneg ((k 2 : ℝ))]

theorem norm_component_le_complexVectorL1 (v : ComplexVector) (component : Fin 3) :
    ‖v component‖ ≤ complexVectorL1 v := by
  unfold complexVectorL1
  fin_cases component <;> simp <;>
    linarith [norm_nonneg (v 0), norm_nonneg (v 1), norm_nonneg (v 2)]

/-- [proved-derived; formal-checked] The derivative multiplier of one mode costs `2π` times the
coordinate length of the frequency times the `ℓ¹` face of the velocity coefficient. -/
theorem norm_fourierJacobianMode_le (k : SpatialFrequency) (v : ComplexVector)
    (J : ComplexJacobianArray)
    (hJ : ∀ component coordinate,
      J component coordinate = (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * v component) :
    ‖J‖ ≤ 2 * Real.pi * frequencyL1 k * complexVectorL1 v := by
  have hnonneg : 0 ≤ 2 * Real.pi * frequencyL1 k * complexVectorL1 v :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (frequencyL1_nonneg k))
      (complexVectorL1_nonneg v)
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro component
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro coordinate
  rw [hJ component coordinate]
  have hscalar : ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ))‖ =
      2 * Real.pi * |(k coordinate : ℝ)| := by
    simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg]
  rw [norm_mul, hscalar]
  have hk := abs_coordinate_le_frequencyL1 k coordinate
  have hv := norm_component_le_complexVectorL1 v component
  have h2pi : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_nonneg
  calc 2 * Real.pi * |(k coordinate : ℝ)| * ‖v component‖
      ≤ 2 * Real.pi * frequencyL1 k * ‖v component‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk h2pi) (norm_nonneg _)
    _ ≤ 2 * Real.pi * frequencyL1 k * complexVectorL1 v :=
        mul_le_mul_of_nonneg_left hv (mul_nonneg h2pi (frequencyL1_nonneg k))

/-! ## The band is paid by the componentwise energy receiver -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}

/-- [proved-derived; formal-checked] The Jacobian band inside the cube of radius `N` is bounded
at every torus point by the circle multiplier, the face generator, and the componentwise `L²`
velocity receiver. -/
theorem norm_openPeriodicJacobianBandProjector_le_exterior
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicJacobianBandProjector solution t (frequencyCube radius) q‖ ≤
      2 * Real.pi * exteriorFaceMass radius * openPeriodicVelocityL2RootReceiver solution t := by
  have hR : 0 ≤ openPeriodicVelocityL2RootReceiver solution t :=
    (complexVectorL1_nonneg _).trans
      (complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver solution t 0)
  calc ‖openPeriodicJacobianBandProjector solution t (frequencyCube radius) q‖
      ≤ ∑ k ∈ frequencyCube radius, ‖openPeriodicJacobianFourierMode solution t k‖ :=
        norm_finiteFourierSynthesis_le_sum_norm _ _ q
    _ ≤ ∑ k ∈ frequencyCube radius,
          2 * Real.pi * frequencyL1 k * openPeriodicVelocityL2RootReceiver solution t := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (norm_fourierJacobianMode_le k (openPeriodicVelocityFourierMode solution t k) _
          (fun component coordinate => by
            rw [openPeriodicJacobianFourierMode_eq_fourierJacobianMode]
            rfl)).trans ?_
        exact mul_le_mul_of_nonneg_left
          (complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver solution t k)
          (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (frequencyL1_nonneg k))
    _ = 2 * Real.pi * exteriorFaceMass radius * openPeriodicVelocityL2RootReceiver solution t := by
        unfold exteriorFaceMass
        rw [Finset.mul_sum, Finset.sum_mul]

/-- [proved-derived; formal-checked] The exterior face of the stretching reading, the part carried
by the modes inside the cube, is paid by the componentwise energy receiver and two `ℓ¹` faces of
the receiving vorticity. -/
theorem norm_openPeriodicFiniteHodgeStrainReading_le_exterior
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicFiniteHodgeStrainReading solution t q (frequencyCube radius)‖ ≤
      (2 * Real.pi * exteriorFaceMass radius * openPeriodicVelocityL2RootReceiver solution t) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  rw [openPeriodicFiniteHodgeStrainReading_eq_symmetricActualJacobianBand]
  erw [complexStretchingReading_symmetricComplexJacobianPart]
  refine (norm_complexStretchingReading_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right
    (norm_openPeriodicJacobianBandProjector_le_exterior solution t radius q) (sq_nonneg _)

/-! ## The split of the aligned strain into exterior and interior faces -/

/-- [proved-derived; formal-checked] **Exterior and interior faces of the aligned strain.**  At
every interior event and every cube radius, the aligned strain differential is at most the
exterior constant `2π · G(N) · 3√(2E₀)`, paid by the initial kinetic energy alone, plus the
interior coefficient tail mass over the complement of the cube, times `9‖ω‖²`.  The exterior
term is constant on the whole lifespan. -/
theorem alignedStrain_le_exterior_add_interior
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) (radius : ℕ) :
    alignedStrain velocity x t ≤
      (2 * Real.pi * exteriorFaceMass radius *
          (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) +
        openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩ (frequencyCube radius)) *
        (9 * ‖vorticityField velocity x t‖ ^ 2) := by
  set q : SpatialTorus := euclideanToSpatialTorus x with hq
  set tt : Ioo 0 T := ⟨t, ht⟩ with htt
  have hproj := openPeriodicPhysicalVortexStretchingAt_projection solution tt x
  have hphys : alignedStrain velocity x t =
      openPeriodicPhysicalVortexStretchingAt solution tt q := hproj.symm
  have habs : |openPeriodicPhysicalVortexStretchingAt solution tt q| =
      ‖openPeriodicFullStrainReading solution tt q‖ :=
    (norm_openPeriodicFullStrainReading_eq_abs_physical solution tt q).symm
  have hsplit := openPeriodicFullStrainReading_eq_finite_add_tail solution tt q
    (frequencyCube radius)
  have hfinite := norm_openPeriodicFiniteHodgeStrainReading_le_exterior solution tt radius q
  have htail : ‖complexStretchingReading (openPeriodicComplexVorticityAt solution tt q)
      (symmetricComplexJacobianPart
        (openPeriodicJacobianArrayFourierTail solution tt (frequencyCube radius) q))‖ ≤
      openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution tt q) ^ 2 := by
    erw [complexStretchingReading_symmetricComplexJacobianPart]
    exact (norm_complexStretchingReading_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (norm_openPeriodicJacobianArrayFourierTail_le solution tt (frequencyCube radius) q)
        (sq_nonneg _))
  have hL2 := openPeriodicVelocityL2RootReceiver_le_kineticEnergy solution tt
  have hE := openPeriodicSolutionOn_periodicKineticEnergy_le_initial solution hnu ht
  have hsqrt : Real.sqrt (2 * periodicKineticEnergy velocity t) ≤
      Real.sqrt (2 * periodicKineticEnergy velocity 0) :=
    Real.sqrt_le_sqrt (by linarith)
  have hL1 : complexVectorL1 (openPeriodicComplexVorticityAt solution tt q) ≤
      3 * ‖vorticityField velocity x t‖ := by
    rw [openPeriodicComplexVorticityAt_eq_torusComplexification, hq,
      torusVorticityEvolution_projection]
    exact complexVectorL1_complexOfRealSpace_le_three_norm _
  have hL1sq : complexVectorL1 (openPeriodicComplexVorticityAt solution tt q) ^ 2 ≤
      9 * ‖vorticityField velocity x t‖ ^ 2 := by
    have h := pow_le_pow_left₀ (complexVectorL1_nonneg _) hL1 2
    linarith [h]
  have hmass : 0 ≤ 2 * Real.pi * exteriorFaceMass radius :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (exteriorFaceMass_nonneg radius)
  have htailNonneg : 0 ≤ openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius) :=
    norm_nonneg _
  have hRle : openPeriodicVelocityL2RootReceiver solution tt ≤
      3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) :=
    hL2.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  calc alignedStrain velocity x t
      = openPeriodicPhysicalVortexStretchingAt solution tt q := hphys
    _ ≤ |openPeriodicPhysicalVortexStretchingAt solution tt q| := le_abs_self _
    _ = ‖openPeriodicFullStrainReading solution tt q‖ := habs
    _ ≤ ‖openPeriodicFiniteHodgeStrainReading solution tt q (frequencyCube radius)‖ +
          ‖complexStretchingReading (openPeriodicComplexVorticityAt solution tt q)
            (symmetricComplexJacobianPart
              (openPeriodicJacobianArrayFourierTail solution tt (frequencyCube radius) q))‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ (2 * Real.pi * exteriorFaceMass radius * openPeriodicVelocityL2RootReceiver solution tt +
          openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution tt q) ^ 2 := by
        rw [add_mul]
        exact add_le_add hfinite htail
    _ ≤ (2 * Real.pi * exteriorFaceMass radius *
            (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) +
          openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius)) *
          (9 * ‖vorticityField velocity x t‖ ^ 2) := by
        have h1 : 2 * Real.pi * exteriorFaceMass radius * openPeriodicVelocityL2RootReceiver solution tt +
              openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius) ≤
            2 * Real.pi * exteriorFaceMass radius *
                (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) +
              openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius) :=
          add_le_add (mul_le_mul_of_nonneg_left hRle hmass) le_rfl
        have h2 : 0 ≤ 2 * Real.pi * exteriorFaceMass radius *
                (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) +
              openPeriodicJacobianCoefficientTailMass solution tt (frequencyCube radius) :=
          add_nonneg (mul_nonneg hmass (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
            htailNonneg
        exact mul_le_mul h1 hL1sq (sq_nonneg _) h2

/-! ## The cube generator in closed form

`G(N) = Σ_{k ∈ cube N} |k|₁ = 3 · (2N+1)² · N (N+1)`.  The three factors are the coordinate
count, the transverse face count, and the one-coordinate generator; no factor is a rounding. -/

/-- The signed coordinate interval `[-N, N]` on the integers. -/
def coordinateInterval (radius : ℕ) : Finset ℤ := Finset.Icc (-(radius : ℤ)) radius

theorem card_coordinateInterval (radius : ℕ) :
    (coordinateInterval radius).card = 2 * radius + 1 := by
  simp [coordinateInterval, Int.card_Icc]
  omega

theorem coordinateInterval_succ (radius : ℕ) :
    coordinateInterval (radius + 1) =
      insert (-((radius : ℤ) + 1)) (insert ((radius : ℤ) + 1) (coordinateInterval radius)) := by
  ext m
  simp only [coordinateInterval, Finset.mem_Icc, Finset.mem_insert]
  push_cast
  omega

/-- The one-coordinate generator: the sum of `|m|` over `[-N, N]` is `N (N + 1)`. -/
theorem sum_abs_coordinateInterval (radius : ℕ) :
    ∑ m ∈ coordinateInterval radius, |(m : ℝ)| = radius * (radius + 1) := by
  induction radius with
  | zero => simp [coordinateInterval]
  | succ n ih =>
    rw [coordinateInterval_succ, Finset.sum_insert, Finset.sum_insert, ih]
    · push_cast
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      ring
    · simp only [coordinateInterval, Finset.mem_Icc, not_and, not_le]
      intro _; omega
    · simp only [coordinateInterval, Finset.mem_Icc, Finset.mem_insert, not_or, not_and, not_le]
      exact ⟨by omega, fun _ => by omega⟩

theorem frequencyCube_eq_piFinset (radius : ℕ) :
    frequencyCube radius = Fintype.piFinset fun _ : Fin 3 => coordinateInterval radius := by
  rw [frequencyCube, Pi.Icc_eq]; rfl

/-- One coordinate face of the cube generator. -/
theorem sum_abs_coordinate_frequencyCube (radius : ℕ) (coordinate : Fin 3) :
    ∑ k ∈ frequencyCube radius, |(k coordinate : ℝ)| =
      (2 * radius + 1) ^ 2 * (radius * (radius + 1)) := by
  rw [frequencyCube_eq_piFinset,
    Finset.sum_comp (fun m : ℤ => |(m : ℝ)|) (fun k : SpatialFrequency => k coordinate),
    Fintype.eval_image_piFinset_const]
  have hfibre : ∀ m ∈ coordinateInterval radius,
      #{k ∈ Fintype.piFinset (fun _ : Fin 3 => coordinateInterval radius) | k coordinate = m} =
        (2 * radius + 1) ^ 2 := by
    intro m hm
    rw [Fintype.card_filter_piFinset_const_eq_of_mem _ _ hm, card_coordinateInterval]
    rfl
  rw [Finset.sum_congr rfl (fun m hm => by rw [hfibre m hm])]
  simp_rw [nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_abs_coordinateInterval]
  push_cast
  ring

/-- **The cube generator in closed form.**  `G(N) = 3 (2N+1)² N (N+1)`: the coordinate count
`3`, the face count `(2N+1)²` transverse to one coordinate, and the one-coordinate generator
`N (N+1)`. -/
theorem exteriorFaceMass_eq (radius : ℕ) :
    exteriorFaceMass radius = 3 * (2 * radius + 1) ^ 2 * (radius * (radius + 1)) := by
  unfold exteriorFaceMass frequencyL1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_abs_coordinate_frequencyCube radius 0, sum_abs_coordinate_frequencyCube radius 1,
    sum_abs_coordinate_frequencyCube radius 2]
  ring

section Audit

#print axioms exteriorFaceMass_eq

#print axioms norm_fourierJacobianMode_le
#print axioms norm_openPeriodicJacobianBandProjector_le_exterior
#print axioms norm_openPeriodicFiniteHodgeStrainReading_le_exterior
#print axioms alignedStrain_le_exterior_add_interior

end Audit

end Soma.Holonics.Millennium.NavierStokesExteriorFaceGenerator
