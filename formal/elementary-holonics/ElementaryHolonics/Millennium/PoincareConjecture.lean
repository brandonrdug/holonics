import Mathlib.Geometry.Manifold.PoincareConjecture

/-!
# The Poincaré conjecture — the solved Millennium object

Mathlib carries the exact topological and smooth statement shapes as `proof_wanted` declarations;
those declarations deliberately create no constants that this project can import as proofs. This
file gives the propositions stable local names. Perelman's mathematical theorem is proved-standard,
while a kernel-checked proof remains open in this Lean project.

The finite rational passage in `Ricci.lean` is not imported here: it contains no three-manifold,
Ricci tensor, surgery, entropy, or conjugate heat kernel and therefore cannot instantiate this
object without a separately founded transport.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PoincareConjecture

open scoped Manifold ContDiff

universe u

/-- The Euclidean model for a three-manifold chart. -/
abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

/-- The unit three-sphere in four-dimensional Euclidean space. -/
abbrev SphereThree : Set (EuclideanSpace ℝ (Fin 4)) :=
  Metric.sphere 0 1

/-- **The topological Poincaré conjecture**, proved mathematically by Perelman: every closed,
simply connected topological three-manifold is homeomorphic to the three-sphere. -/
def ThePoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ SphereThree)

/-- The smooth companion in dimension three. -/
def TheSmoothPoincareTheorem : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ SphereThree)

end Soma.Holonics.Millennium.PoincareConjecture
