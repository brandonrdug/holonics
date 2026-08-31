import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Platonic face incidence and exact cyclic diffraction

The five Platonic species determine two independent finite incidences used here: the population of
faces and the cyclic order around each face.  The user's hyper-lift count is recorded exactly as
`faceCount * 2 ^ faceOrder`; it is an addressed combinatorial face, not the ordinary vertex count.

For an equal-amplitude face orbit with constant phase step `zeta`, the exact complex structure
factor is a geometric sum.  Whenever `zeta` is a nontrivial root of unity of the face order, the
face contribution vanishes.  Removing one aperture returns the negative of precisely that missing
ray.  Thus a diffraction zero is a cancellation receiver with a complete coefficient/address
fibre, and a cut reopens it deterministically.

This owner supplies the cyclic face archetype.  A three-dimensional crystal realization must add
its actual vertex positions, scattering weights, reciprocal-lattice covector, and receiver chart;
those data determine the full diffraction pattern.
-/

namespace Soma.Holonics.Millennium.HolonicPlatonicDiffraction

open scoped BigOperators

/-- The five regular convex polyhedral species. -/
inductive PlatonicSolid
  | tetrahedron
  | cube
  | octahedron
  | icosahedron
  | dodecahedron
deriving DecidableEq, Repr

/-- Number of ordinary geometric faces. -/
def faceCount : PlatonicSolid → ℕ
  | .tetrahedron => 4
  | .cube => 6
  | .octahedron => 8
  | .icosahedron => 20
  | .dodecahedron => 12

/-- Cyclic order of the polygon bounding each face. -/
def faceOrder : PlatonicSolid → ℕ
  | .tetrahedron => 3
  | .cube => 4
  | .octahedron => 3
  | .icosahedron => 3
  | .dodecahedron => 5

/-- The user's lifted causal-incidence population: one binary incidence population per face pin. -/
def hyperLiftPopulation (solid : PlatonicSolid) : ℕ :=
  faceCount solid * 2 ^ faceOrder solid

/-- Exact values of all five supplied hyper-lift populations. -/
theorem platonicHyperLiftPopulationLedger :
    hyperLiftPopulation .tetrahedron = 32 ∧
      hyperLiftPopulation .cube = 96 ∧
      hyperLiftPopulation .octahedron = 64 ∧
      hyperLiftPopulation .icosahedron = 160 ∧
      hyperLiftPopulation .dodecahedron = 384 := by
  decide

/-- The exact complex amplitude of one equal-amplitude cyclic aperture orbit. -/
def cyclicAmplitude (order : ℕ) (amplitude phaseStep : ℂ) : ℂ :=
  ∑ index ∈ Finset.range order, amplitude * phaseStep ^ index

/-- Pull the common amplitude outside the complete phase-incidence population. -/
theorem cyclicAmplitude_eq_amplitude_mul_geomSum
    (order : ℕ) (amplitude phaseStep : ℂ) :
    cyclicAmplitude order amplitude phaseStep =
      amplitude * ∑ index ∈ Finset.range order, phaseStep ^ index := by
  simp only [cyclicAmplitude, Finset.mul_sum]

/-- A complete nontrivial cyclic character cancels exactly. -/
theorem cyclicAmplitude_eq_zero
    {order : ℕ} {amplitude phaseStep : ℂ}
    (closes : phaseStep ^ order = 1) (nontrivial : phaseStep ≠ 1) :
    cyclicAmplitude order amplitude phaseStep = 0 := by
  rw [cyclicAmplitude_eq_amplitude_mul_geomSum, geom_sum_eq nontrivial,
    closes, sub_self, zero_div, mul_zero]

/-- The same face amplitude repeated over every face of one Platonic species. -/
def platonicFaceAmplitude
    (solid : PlatonicSolid) (amplitude phaseStep : ℂ) : ℂ :=
  (faceCount solid : ℂ) * cyclicAmplitude (faceOrder solid) amplitude phaseStep

/-- Complete cyclic cancellation on every face forces the repeated face receiver to zero. -/
theorem platonicFaceAmplitude_eq_zero
    (solid : PlatonicSolid) {amplitude phaseStep : ℂ}
    (closes : phaseStep ^ faceOrder solid = 1) (nontrivial : phaseStep ≠ 1) :
    platonicFaceAmplitude solid amplitude phaseStep = 0 := by
  rw [platonicFaceAmplitude, cyclicAmplitude_eq_zero closes nontrivial, mul_zero]

/-- Remove one addressed aperture from the cyclic population. -/
def cutCyclicAmplitude
    (order missing : ℕ) (amplitude phaseStep : ℂ) : ℂ :=
  ∑ index ∈ (Finset.range order).erase missing, amplitude * phaseStep ^ index

/--
Cutting one site from a cancelling orbit returns exactly the oppositely oriented missing ray.

The result is not a perturbative estimate: the full orbit, the removed address, and the returned
complex difference remain explicit.
-/
theorem cutCyclicAmplitude_eq_neg_missingRay
    {order missing : ℕ} {amplitude phaseStep : ℂ}
    (missing_mem : missing < order)
    (closes : phaseStep ^ order = 1) (nontrivial : phaseStep ≠ 1) :
    cutCyclicAmplitude order missing amplitude phaseStep =
      -(amplitude * phaseStep ^ missing) := by
  have membership : missing ∈ Finset.range order := Finset.mem_range.mpr missing_mem
  have decomposition := Finset.sum_erase_add (Finset.range order)
    (fun index ↦ amplitude * phaseStep ^ index) membership
  change cutCyclicAmplitude order missing amplitude phaseStep +
      amplitude * phaseStep ^ missing = cyclicAmplitude order amplitude phaseStep at decomposition
  rw [cyclicAmplitude_eq_zero closes nontrivial] at decomposition
  exact eq_neg_of_add_eq_zero_left decomposition

/-- A nonzero missing ray necessarily reopens the former diffraction zero. -/
theorem cutCyclicAmplitude_ne_zero
    {order missing : ℕ} {amplitude phaseStep : ℂ}
    (missing_mem : missing < order)
    (closes : phaseStep ^ order = 1) (nontrivial : phaseStep ≠ 1)
    (ray_nonzero : amplitude * phaseStep ^ missing ≠ 0) :
    cutCyclicAmplitude order missing amplitude phaseStep ≠ 0 := by
  rw [cutCyclicAmplitude_eq_neg_missingRay missing_mem closes nontrivial]
  exact neg_ne_zero.mpr ray_nonzero

section Audit

#print axioms platonicHyperLiftPopulationLedger
#print axioms cyclicAmplitude_eq_zero
#print axioms platonicFaceAmplitude_eq_zero
#print axioms cutCyclicAmplitude_eq_neg_missingRay
#print axioms cutCyclicAmplitude_ne_zero

end Audit

end Soma.Holonics.Millennium.HolonicPlatonicDiffraction
