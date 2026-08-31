import ElementaryHolonics.Millennium.HilbertTransportRefinement
import ElementaryHolonics.Millennium.YangMillsLimit
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Yang--Mills structured construction receiver

[counterexample; source-audit] `YangMills.Problem` records the shape of a supplied problem, but its admission
predicates and energy spectrum are arbitrary.  Consequently it is not a non-vacuous closed Clay
receiver.  This file removes those two failure modes:

* [definition] a gauge-group occurrence carries actual `Group`, `IsTopologicalGroup`, compactness,
  connectedness, finite-dimensional smooth `LieGroup`, and simple-Lie-algebra structures; and
* [definition] the energy spectrum is derived from a densely defined symmetric Hamiltonian as its approximate
  point spectrum.  It is not a caller-supplied set.

[definition] The continuum theory object also carries a gauge/translation action, invariant Euclidean
action and expectation, reflection positivity, a nonzero observable, and the reconstructed
Hamiltonian.  The closed `YangMillsConstructionFinishLine` explicitly requires the gauge-source
type to be inhabited before universally constructing a gapped theory, so an empty domain cannot
prove it.

[open] This remains a repository construction finish line rather than a claimed formal equivalent of the
Clay statement.  Mathlib does not yet identify the Lie bracket on a chart model with the canonical
tangent Lie algebra of a `LieGroup`, formalize distribution-valued four-dimensional gauge fields,
or provide Osterwalder--Schrader reconstruction and unbounded self-adjoint spectral theory.  The
structures below expose those missing ports without replacing them by admission predicates.
-/

noncomputable section

open scoped Manifold

namespace Soma.Holonics.Millennium.YangMillsOfficialReceiver

open Soma.Holonics.Millennium.YangMillsLimit

universe u v w

/-- [definition] An intrinsically structured compact connected gauge-group source with a simple
Lie algebra on the same finite-dimensional model used by its smooth Lie-group chart.

The final identification of this bracket with Mathlib's not-yet-bundled tangent Lie algebra is the
explicit remaining group-source faithfulness boundary; there is no Boolean admission field. -/
structure CompactConnectedSimpleGaugeGroup where
  Carrier : Type u
  Model : Type v
  carrierGroup : Group Carrier
  carrierTopology : TopologicalSpace Carrier
  carrierTopologicalGroup : IsTopologicalGroup Carrier
  carrierT2 : T2Space Carrier
  carrierCompact : CompactSpace Carrier
  carrierConnected : ConnectedSpace Carrier
  modelNormedAddCommGroup : NormedAddCommGroup Model
  modelNormedSpace : NormedSpace ℝ Model
  modelFiniteDimensional : FiniteDimensional ℝ Model
  carrierChartedSpace : ChartedSpace Model Carrier
  carrierIsManifold : IsManifold (modelWithCornersSelf ℝ Model) ω Carrier
  carrierLieGroup : LieGroup (modelWithCornersSelf ℝ Model) ω Carrier
  modelLieRing : LieRing Model
  modelLieAlgebra : LieAlgebra ℝ Model
  modelSimple : LieAlgebra.IsSimple ℝ Model

namespace CompactConnectedSimpleGaugeGroup

attribute [instance] carrierGroup carrierTopology carrierTopologicalGroup carrierCompact
  carrierT2 carrierConnected modelNormedAddCommGroup modelNormedSpace modelFiniteDimensional
  carrierChartedSpace carrierIsManifold carrierLieGroup modelLieRing modelLieAlgebra modelSimple

end CompactConnectedSimpleGaugeGroup

/-- [definition] A densely defined positive symmetric Hamiltonian on a complete complex Hilbert
space.  The spectrum below is derived from this operator by approximate eigenvectors.

Full equality between the operator and its unbounded adjoint is not encoded because Mathlib has no
corresponding owner; `symmetric` and `dense_domain` are retained as the precise current boundary. -/
structure ContinuumHamiltonian where
  Hilbert : Type w
  hilbertNormedAddCommGroup : NormedAddCommGroup Hilbert
  hilbertInnerProductSpace : InnerProductSpace ℂ Hilbert
  hilbertCompleteSpace : CompleteSpace Hilbert
  domain : Submodule ℂ Hilbert
  dense_domain : Dense (domain : Set Hilbert)
  action : domain →ₗ[ℂ] Hilbert
  symmetric : ∀ x y : domain,
    inner ℂ (action x) (y : Hilbert) = inner ℂ (x : Hilbert) (action y)
  nonnegative : ∀ x : domain,
    0 ≤ Complex.re (inner ℂ (x : Hilbert) (action x))
  vacuum : domain
  vacuum_normalized : ‖(vacuum : Hilbert)‖ = 1
  vacuum_energy_zero : action vacuum = 0

namespace ContinuumHamiltonian

attribute [instance] hilbertNormedAddCommGroup hilbertInnerProductSpace hilbertCompleteSpace

/-- [definition] `mu` belongs to the operator's approximate point spectrum when unit domain
vectors can make `(H - mu) psi` arbitrarily small. -/
def IsApproximateEnergy (H : ContinuumHamiltonian) (mu : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ psi : H.domain,
      ‖(psi : H.Hilbert)‖ = 1 ∧
        ‖H.action psi - (mu : ℂ) • (psi : H.Hilbert)‖ < epsilon

/-- [definition] The energy spectrum is a derived receiver of the Hamiltonian, not independent
input data. -/
def energySpectrum (H : ContinuumHamiltonian) : Set ℝ :=
  {mu | H.IsApproximateEnergy mu}

/-- [proved-derived; formal-checked] The normalized zero-energy vacuum puts zero in the derived
spectrum. -/
theorem zero_mem_energySpectrum (H : ContinuumHamiltonian) :
    0 ∈ H.energySpectrum := by
  intro epsilon hepsilon
  refine ⟨H.vacuum, H.vacuum_normalized, ?_⟩
  simp [H.vacuum_energy_zero, hepsilon]

/-- [definition] The exact positive-gap receiver on the Hamiltonian-derived spectrum. -/
def HasMassGap (H : ContinuumHamiltonian) : Prop :=
  SpectrumHasMassGap H.energySpectrum

end ContinuumHamiltonian

/-- [definition] Structured continuum Euclidean Yang--Mills/QFT construction over one genuine
gauge-group source.

The expectation is an actual complex-linear functional on configuration observables.  Reflection
positivity is stated on a retained positive-time observable carrier, and the Hamiltonian is an
operator whose spectrum is subsequently derived.  No field of type `isYangMills : Prop`,
`satisfiesAxioms : Prop`, or caller-authored `energySpectrum` occurs. -/
structure ContinuumYangMillsTheory
    (G : CompactConnectedSimpleGaugeGroup.{u, v}) where
  Configuration : Type u
  gaugeTransform : G.Carrier → Configuration → Configuration
  gauge_one : ∀ configuration, gaugeTransform 1 configuration = configuration
  gauge_mul : ∀ left right configuration,
    gaugeTransform (left * right) configuration =
      gaugeTransform left (gaugeTransform right configuration)
  translate : (Fin 4 → ℝ) → Configuration → Configuration
  translate_zero : ∀ configuration, translate 0 configuration = configuration
  translate_add : ∀ left right configuration,
    translate (left + right) configuration =
      translate left (translate right configuration)
  gauge_translate_commute : ∀ gauge displacement configuration,
    gaugeTransform gauge (translate displacement configuration) =
      translate displacement (gaugeTransform gauge configuration)
  euclideanAction : Configuration → ℝ
  action_gauge_invariant : ∀ gauge configuration,
    euclideanAction (gaugeTransform gauge configuration) = euclideanAction configuration
  action_translation_invariant : ∀ displacement configuration,
    euclideanAction (translate displacement configuration) = euclideanAction configuration
  PositiveTimeObservable : Type v
  observableNormedAddCommGroup : NormedAddCommGroup PositiveTimeObservable
  observableNormedSpace : NormedSpace ℂ PositiveTimeObservable
  evaluate : PositiveTimeObservable →ₗ[ℂ] (Configuration → ℂ)
  timeReflection : Configuration → Configuration
  timeReflection_involutive : Function.Involutive timeReflection
  expectation : (Configuration → ℂ) →ₗ[ℂ] ℂ
  expectation_gauge_invariant : ∀ gauge observable,
    expectation (fun configuration => observable (gaugeTransform gauge configuration)) =
      expectation observable
  expectation_translation_invariant : ∀ displacement observable,
    expectation (fun configuration => observable (translate displacement configuration)) =
      expectation observable
  reflection_positive : ∀ observable : PositiveTimeObservable,
    0 ≤ Complex.re
      (expectation (fun configuration =>
        star (evaluate observable (timeReflection configuration)) *
          evaluate observable configuration))
  nontrivial_observable : ∃ observable : PositiveTimeObservable, evaluate observable ≠ 0
  hamiltonian : ContinuumHamiltonian.{w}
  /-- Euclidean time transport on the positive-time observable current. -/
  euclideanTimeTranslate : ℝ → PositiveTimeObservable →ₗ[ℂ] PositiveTimeObservable
  timeTranslate_zero : euclideanTimeTranslate 0 = LinearMap.id
  timeTranslate_add : ∀ left right,
    euclideanTimeTranslate (left + right) =
      (euclideanTimeTranslate left).comp (euclideanTimeTranslate right)
  /-- The infinitesimal Euclidean-time current before OS reconstruction. -/
  euclideanTimeGenerator : PositiveTimeObservable →ₗ[ℂ] PositiveTimeObservable
  timeTranslate_hasGenerator : ∀ observable : PositiveTimeObservable,
    HasDerivAt (fun time : ℝ => euclideanTimeTranslate time observable)
      (euclideanTimeGenerator observable) 0
  /-- The OS quotient/reconstruction map into the same Hilbert carrier on which the Hamiltonian
  acts. -/
  positiveTimeToHilbert : PositiveTimeObservable →ₗ[ℂ] hamiltonian.Hilbert
  positiveTimeToHilbert_dense : Dense (Set.range positiveTimeToHilbert)
  os_inner : ∀ left right : PositiveTimeObservable,
    inner ℂ (positiveTimeToHilbert left) (positiveTimeToHilbert right) =
      expectation (fun configuration =>
        star (evaluate left (timeReflection configuration)) *
          evaluate right configuration)
  /-- Every reconstructed positive-time observable is retained in the Hamiltonian domain. -/
  positiveTimeToDomain : PositiveTimeObservable →ₗ[ℂ] hamiltonian.domain
  positiveTimeToDomain_coe : ∀ observable,
    ((positiveTimeToDomain observable : hamiltonian.domain) : hamiltonian.Hilbert) =
      positiveTimeToHilbert observable
  /-- The Hamiltonian is the reconstructed infinitesimal Euclidean-time generator on the dense
  OS current, rather than an independent gapped operator. -/
  hamiltonian_is_reconstructed_generator : ∀ observable,
    hamiltonian.action (positiveTimeToDomain observable) =
      positiveTimeToHilbert (euclideanTimeGenerator observable)
  spectrum_nonnegative : ∀ mu ∈ hamiltonian.energySpectrum, 0 ≤ mu

namespace ContinuumYangMillsTheory

attribute [instance] observableNormedAddCommGroup observableNormedSpace

/-- [proved-derived; formal-checked] A theory-level gap return has the literal Hamiltonian-derived
spectrum required by the structured receiver. -/
theorem hasMassGap_returns_separator
    {G : CompactConnectedSimpleGaugeGroup}
    (Q : ContinuumYangMillsTheory G)
    (hgap : Q.hamiltonian.HasMassGap) :
    ∃ Delta : ℝ, 0 < Delta ∧
      ∀ mu ∈ Q.hamiltonian.energySpectrum, mu = 0 ∨ Delta ≤ mu :=
  hgap.2.2.2

end ContinuumYangMillsTheory

/-- [definition] The non-vacuous closed repository finish line for Yang--Mills construction.

The first conjunct rules out the old empty-gauge-domain proof.  The universal clause ranges only
over objects already carrying actual compact/connected/topological/Lie/simple structure, and its
spectrum is forced to be the approximate spectrum of the returned Hamiltonian. -/
def YangMillsConstructionFinishLine : Prop :=
  Nonempty (CompactConnectedSimpleGaugeGroup.{u, v}) ∧
    ∀ G : CompactConnectedSimpleGaugeGroup.{u, v},
      ∃ Q : ContinuumYangMillsTheory.{u, v, w} G, Q.hamiltonian.HasMassGap

namespace YangMillsConstructionFinishLine

/-- [proved-derived; formal-checked] The closed finish line cannot be discharged by an empty
gauge-group source type. -/
theorem gauge_source_nonempty
    (h : YangMillsConstructionFinishLine.{u, v, w}) :
    Nonempty (CompactConnectedSimpleGaugeGroup.{u, v}) :=
  h.1

/-- [proved-derived; formal-checked] Every intrinsically structured gauge source receives one
continuum theory with a Hamiltonian-derived positive mass gap. -/
theorem theory_for
    (h : YangMillsConstructionFinishLine.{u, v, w})
    (G : CompactConnectedSimpleGaugeGroup.{u, v}) :
    ∃ Q : ContinuumYangMillsTheory.{u, v, w} G,
      Q.hamiltonian.HasMassGap :=
  h.2 G

end YangMillsConstructionFinishLine

/-- [definition] A lawful finite-to-continuum spectral reconstruction receipt.

Uniform finite gaps alone are insufficient.  Every nonzero continuum spectral occurrence must
return a nonzero finite ancestor below it; this retained lineage transports the same separator
into the continuum. -/
structure FiniteContinuumReconstruction (H : ContinuumHamiltonian)
    (Scale : Type u) [Nonempty Scale] where
  finiteSpectrum : Scale → Set ℝ
  separator : ℝ
  separator_positive : 0 < separator
  finite_vacuum : ∀ scale, 0 ∈ finiteSpectrum scale
  finite_uniform_gap : ∀ scale mu, mu ∈ finiteSpectrum scale →
    mu = 0 ∨ separator ≤ mu
  continuum_nonzero_ancestor : ∀ mu, mu ∈ H.energySpectrum → mu ≠ 0 →
    ∃ scale ancestor,
      ancestor ∈ finiteSpectrum scale ∧ ancestor ≠ 0 ∧ ancestor ≤ mu
  continuum_nonnegative : ∀ mu ∈ H.energySpectrum, 0 ≤ mu
  continuum_excitation : ∃ mu ∈ H.energySpectrum, 0 < mu

namespace FiniteContinuumReconstruction

/-- [proved-derived; formal-checked] Uniform finite separation plus nonzero ancestor lineage
returns the positive gap on the Hamiltonian-derived continuum spectrum. -/
theorem toContinuumMassGap
    {H : ContinuumHamiltonian} {Scale : Type u} [Nonempty Scale]
    (R : FiniteContinuumReconstruction H Scale) :
    H.HasMassGap := by
  refine ⟨H.zero_mem_energySpectrum, R.continuum_nonnegative,
    R.continuum_excitation, R.separator, R.separator_positive, ?_⟩
  intro mu hmu
  by_cases hzero : mu = 0
  · exact Or.inl hzero
  · right
    obtain ⟨scale, ancestor, hancestor, hancestor_nonzero, hbelow⟩ :=
      R.continuum_nonzero_ancestor mu hmu hzero
    exact (R.finite_uniform_gap scale ancestor hancestor).resolve_left hancestor_nonzero |>.trans hbelow

end FiniteContinuumReconstruction

end Soma.Holonics.Millennium.YangMillsOfficialReceiver
