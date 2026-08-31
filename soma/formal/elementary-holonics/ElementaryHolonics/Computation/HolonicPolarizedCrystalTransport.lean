import ElementaryHolonics.Computation.HolonicOrientedSiteTransport
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Coherent polarized paths through crystalline interiors to surface receivers

**[proved-derived]** A finite path family retains source and surface boundary maps, one complete
complex polarization transport per path, path amplitude, and path identity.  All histories reaching
one addressed surface join linearly before an analyzer or intensity receiver is applied.  A crystal
adds exact positions and spatial phase; it does not replace polarization transport or path lineage.

The construction is a finite path sum.  It proves no continuum path-integral limit, Maxwell
calibration, material dispersion law, stochastic diffusion law, or identification of information
current with physical light.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicPolarizedCrystalTransport

open scoped BigOperators ComplexConjugate Matrix

universe uPath uSource uSurface uPol uDim

/-- [definition] A finite coherent path population with both boundary maps retained. -/
structure FiniteCoherentPathFamily
    (Path : Type uPath) (Source : Type uSource) (Surface : Type uSurface)
    (Polarization : Type uPol) where
  source : Path → Source
  surface : Path → Surface
  transport : Path → Matrix Polarization Polarization ℂ
  amplitude : Path → ℂ

namespace FiniteCoherentPathFamily

variable {Path : Type uPath} {Source : Type uSource} {Surface : Type uSurface}
  {Polarization : Type uPol}
  [Fintype Path] [DecidableEq Source] [DecidableEq Surface]
  [Fintype Polarization] [DecidableEq Polarization]
  (family : FiniteCoherentPathFamily Path Source Surface Polarization)

/-- [definition] Every retained path with the addressed source and surface boundaries. -/
def boundaryFiber (source : Source) (surface : Surface) : Finset Path :=
  Finset.univ.filter fun path ↦ family.source path = source ∧ family.surface path = surface

/-- [definition] The complete polarization section carried by one path. -/
def carried (path : Path) (input : Polarization → ℂ) : Polarization → ℂ :=
  family.amplitude path • (family.transport path *ᵥ input)

/-- [definition] The coherent section at one addressed surface junction. -/
def surfaceSection (source : Source) (surface : Surface) (input : Polarization → ℂ) :
    Polarization → ℂ :=
  ∑ path ∈ family.boundaryFiber source surface, family.carried path input

/-- The surface section reconstructs exactly from the path fibre retaining both boundary maps. -/
theorem surfaceSection_eq_sum_boundaryFiber
    (source : Source) (surface : Surface) (input : Polarization → ℂ) :
    family.surfaceSection source surface input =
      ∑ path ∈ family.boundaryFiber source surface, family.carried path input := rfl

/-- [definition] A polarization analyzer is a receiver covector. -/
def analyze (analyzer state : Polarization → ℂ) : ℂ :=
  ∑ polarization, conj (analyzer polarization) * state polarization

/-- [definition] The complex analyzer face of the complete coherent surface section. -/
def surfaceAmplitude (source : Source) (surface : Surface)
    (input analyzer : Polarization → ℂ) : ℂ :=
  analyze analyzer (family.surfaceSection source surface input)

/-- [definition] Intensity is the norm-square receiver applied only after coherent path joining and
polarization analysis. -/
def surfaceIntensity (source : Source) (surface : Surface)
    (input analyzer : Polarization → ℂ) : ℝ :=
  Complex.normSq (family.surfaceAmplitude source surface input analyzer)

/-- The receiver order is exposed definitionally: path currents join, the analyzer acts, and only
then is norm-square formed. -/
theorem surfaceIntensity_eq_normSq_analyze_joined
    (source : Source) (surface : Surface)
    (input analyzer : Polarization → ℂ) :
    family.surfaceIntensity source surface input analyzer =
      Complex.normSq
        (analyze analyzer
          (∑ path ∈ family.boundaryFiber source surface, family.carried path input)) := rfl

end FiniteCoherentPathFamily

/-! ## Ordered local transport and basis rebase -/

variable {Polarization : Type uPol} [Fintype Polarization] [DecidableEq Polarization]

/-- [definition] Chronological composition: `first` acts before `second`. -/
def composeTransport
    (first second : Matrix Polarization Polarization ℂ) : Matrix Polarization Polarization ℂ :=
  second * first

/-- Composed path transport acts in chronological order on the carried section. -/
theorem composeTransport_mulVec
    (first second : Matrix Polarization Polarization ℂ) (input : Polarization → ℂ) :
    composeTransport first second *ᵥ input = second *ᵥ (first *ᵥ input) := by
  exact (Matrix.mulVec_mulVec input second first).symm

/-- [definition] An exact polarization-chart rebase with both inverse laws. -/
structure PolarizationRebase where
  forward : Matrix Polarization Polarization ℂ
  backward : Matrix Polarization Polarization ℂ
  backward_forward : backward * forward = 1
  forward_backward : forward * backward = 1

namespace PolarizationRebase

/-- [definition] Transport the local law through the declared polarization chart. -/
def transport (rebase : PolarizationRebase (Polarization := Polarization))
    (operator : Matrix Polarization Polarization ℂ) : Matrix Polarization Polarization ℂ :=
  rebase.forward * operator * rebase.backward

/-- Exact basis covariance: rebasing the law and input rebases the returned section. -/
theorem transport_mulVec_forward
    (rebase : PolarizationRebase (Polarization := Polarization))
    (operator : Matrix Polarization Polarization ℂ) (input : Polarization → ℂ) :
    rebase.transport operator *ᵥ (rebase.forward *ᵥ input) =
      rebase.forward *ᵥ (operator *ᵥ input) := by
  simp only [transport, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc (rebase.forward * operator) rebase.backward rebase.forward,
    rebase.backward_forward, Matrix.mul_one]

end PolarizationRebase

/-! ## Crystalline phase on any finite path population -/

variable {Path : Type uPath} [Fintype Path]
  {Dimension : Type uDim} [Fintype Dimension]

/-- [definition] Exact spatial phase of one path occurrence. -/
def crystallinePhase (position : Path → Dimension → ℝ)
    (waveVector : Dimension → ℝ) (path : Path) : ℂ :=
  Complex.exp (Complex.I *
    (∑ coordinate : Dimension,
      (waveVector coordinate * position path coordinate : ℝ) : ℂ))

/-- [definition] Exact finite crystalline diffraction amplitude. -/
def crystallineAmplitude (coefficient : Path → ℂ) (position : Path → Dimension → ℝ)
    (waveVector : Dimension → ℝ) : ℂ :=
  ∑ path : Path, coefficient path * crystallinePhase position waveVector path

/-- [definition] The later intensity face of the complete crystalline amplitude. -/
def crystallineIntensity (coefficient : Path → ℂ) (position : Path → Dimension → ℝ)
    (waveVector : Dimension → ℝ) : ℝ :=
  Complex.normSq (crystallineAmplitude coefficient position waveVector)

/-! ## Exact controls -/

abbrev JonesPolarization := Fin 2
abbrev JonesSection := JonesPolarization → ℂ

def horizontal : JonesSection := ![1, 0]
def vertical : JonesSection := ![0, 1]

/-- Orthogonal analyzers separate the same polarized section. -/
theorem polarization_receivers_separate :
    FiniteCoherentPathFamily.analyze horizontal horizontal = 1 ∧
      FiniteCoherentPathFamily.analyze vertical horizontal = 0 := by
  constructor <;> norm_num [FiniteCoherentPathFamily.analyze, horizontal, vertical,
    Fin.sum_univ_two]

/-- The two paths of the interference control. -/
abbrev TwoPath := Bool

def cancellationFamily : FiniteCoherentPathFamily TwoPath Unit Unit Unit where
  source _ := ()
  surface _ := ()
  transport _ := 1
  amplitude path := if path then 1 else -1

def reinforcementFamily : FiniteCoherentPathFamily TwoPath Unit Unit Unit where
  source _ := ()
  surface _ := ()
  transport _ := 1
  amplitude _ := 1

def scalarInput : Unit → ℂ := fun _ ↦ 1
def scalarAnalyzer : Unit → ℂ := fun _ ↦ 1

/-- Opposite path amplitudes cancel before the intensity receiver, while equal amplitudes reinforce
to intensity four. -/
theorem twoPath_cancellation_and_reinforcement :
    cancellationFamily.surfaceAmplitude () () scalarInput scalarAnalyzer = 0 ∧
      cancellationFamily.surfaceIntensity () () scalarInput scalarAnalyzer = 0 ∧
      reinforcementFamily.surfaceAmplitude () () scalarInput scalarAnalyzer = 2 ∧
      reinforcementFamily.surfaceIntensity () () scalarInput scalarAnalyzer = 4 := by
  norm_num [FiniteCoherentPathFamily.surfaceAmplitude,
    FiniteCoherentPathFamily.surfaceIntensity, FiniteCoherentPathFamily.analyze,
    FiniteCoherentPathFamily.surfaceSection, FiniteCoherentPathFamily.boundaryFiber,
    FiniteCoherentPathFamily.carried, cancellationFamily, reinforcementFamily,
    scalarInput, scalarAnalyzer, Matrix.one_mulVec, Complex.normSq, Fintype.sum_bool]

section Audit

#print axioms FiniteCoherentPathFamily.surfaceSection_eq_sum_boundaryFiber
#print axioms FiniteCoherentPathFamily.surfaceIntensity_eq_normSq_analyze_joined
#print axioms composeTransport_mulVec
#print axioms PolarizationRebase.transport_mulVec_forward
#print axioms polarization_receivers_separate
#print axioms twoPath_cancellation_and_reinforcement

end Audit

end Soma.Holonics.Computation.HolonicPolarizedCrystalTransport
