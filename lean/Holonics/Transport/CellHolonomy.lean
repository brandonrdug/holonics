import Holonics.Foundation.HodgeReceiver
import Holonics.Transport.GeneratorTraceFaces
import Mathlib.Tactic

/-!
# Cell holonomy and harmonic standing at the declared node/cell receivers

[definition] A field on a complex carries transports on its edges. The **face** read at a
two-cell is the holonomy of those transports around it. Regauging the vertices conjugates that
holonomy, so its class functions are the gauge-free faces; a pure gauge has trivial holonomy;
in a commutative carrier the holonomy itself is gauge-free. In the additive chart of
`Foundation/HodgeReceiver`, the flux `d₁A` through every cell is unchanged by a potential
`d₀φ`, and a harmonic mode has no flux through any cell and no divergence at any node while no
potential reproduces it. Relative to this declared node/cell receiver, that harmonic mode is a
dormant standing retained by its class; the statement does not identify every standing mode with a
harmonic cochain.

[established-bounded; formal-checked] Scope: group identities on one triangular cell, matrix
class functions, and the existing finite weighted complex over ℚ. Continuum connections,
curvature forms and characteristic classes are outside this module. No `axiom`, no `sorry`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Holonics.Transport.CellHolonomy

/-! ## 1. Holonomy around a triangular cell -/

section Group

variable {G : Type*} [Group G]

/-- [definition] The holonomy around a triangular cell with edge transports `g₀₁`, `g₁₂`,
`g₂₀`, based at vertex `0`. -/
def triangleHolonomy (g01 g12 g20 : G) : G := g01 * g12 * g20

/-- [definition] Regauging an edge transport by vertex frames `kᵢ`, `kⱼ`. -/
def regauge (ki kj g : G) : G := ki⁻¹ * g * kj

/-- [proved-derived; formal-checked] **Regauging conjugates the holonomy** by the frame at the
base vertex. -/
theorem triangleHolonomy_regauge (k0 k1 k2 g01 g12 g20 : G) :
    triangleHolonomy (regauge k0 k1 g01) (regauge k1 k2 g12) (regauge k2 k0 g20)
      = k0⁻¹ * triangleHolonomy g01 g12 g20 * k0 := by
  simp only [triangleHolonomy, regauge]
  group

/-- [proved-derived; formal-checked] **A pure gauge has trivial holonomy.** -/
theorem pure_gauge_has_trivial_holonomy (k0 k1 k2 : G) :
    triangleHolonomy (regauge k0 k1 1) (regauge k1 k2 1) (regauge k2 k0 1) = 1 := by
  simp only [triangleHolonomy, regauge]
  group

end Group

/-- [proved-derived; formal-checked] In a commutative carrier the holonomy itself is gauge-free:
the phase flux through a cell is a face of the field, not of the chosen frames. -/
theorem abelian_holonomy_is_gauge_free {A : Type*} [CommGroup A] (k0 k1 k2 g01 g12 g20 : A) :
    triangleHolonomy (regauge k0 k1 g01) (regauge k1 k2 g12) (regauge k2 k0 g20)
      = triangleHolonomy g01 g12 g20 := by
  rw [triangleHolonomy_regauge, mul_comm k0⁻¹, mul_assoc, inv_mul_cancel, mul_one]

section MatrixFaces

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- [proved-derived; formal-checked] **The trace of a matrix holonomy is a gauge-free face.** -/
theorem holonomy_trace_is_gauge_free (k0 k1 k2 g01 g12 g20 : (Matrix ι ι R)ˣ) :
    ((triangleHolonomy (regauge k0 k1 g01) (regauge k1 k2 g12) (regauge k2 k0 g20) :
        (Matrix ι ι R)ˣ) : Matrix ι ι R).trace
      = ((triangleHolonomy g01 g12 g20 : (Matrix ι ι R)ˣ) : Matrix ι ι R).trace := by
  rw [triangleHolonomy_regauge]
  simp only [Units.val_mul]
  exact Matrix.trace_units_conj' k0 _

/-- [proved-derived; formal-checked] **The determinant of a matrix holonomy is a gauge-free
face.** -/
theorem holonomy_determinant_is_gauge_free (k0 k1 k2 g01 g12 g20 : (Matrix ι ι R)ˣ) :
    ((triangleHolonomy (regauge k0 k1 g01) (regauge k1 k2 g12) (regauge k2 k0 g20) :
        (Matrix ι ι R)ˣ) : Matrix ι ι R).det
      = ((triangleHolonomy g01 g12 g20 : (Matrix ι ι R)ˣ) : Matrix ι ι R).det := by
  rw [triangleHolonomy_regauge]
  simp only [Units.val_mul]
  exact Matrix.det_units_conj' k0 _

end MatrixFaces

/-! ## 2. Flux through cells and the dormant harmonic mode -/

section Hodge

open Holonics.Foundation.HodgeReceiver

variable {p q r : ℕ} (C : WeightedComplex p q r)

/-- [proved-derived; formal-checked] **The flux through every cell is unchanged by a
potential.** Adding `d₀φ` to an edge field changes no cell reading. -/
theorem cell_flux_is_gauge_free (A : Fin q → ℚ) (φ : Fin p → ℚ) :
    C.d₁ *ᵥ (A + C.d₀ *ᵥ φ) = C.d₁ *ᵥ A := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, C.dd, Matrix.zero_mulVec, add_zero]

/-- [proved-derived; formal-checked] **Harmonic standing is silent at the declared node/cell receivers.** A
harmonic edge field has no flux through any cell and no divergence at any node. -/
theorem dormant_mode_is_locally_silent {h : Fin q → ℚ} (hh : h ∈ C.harmonic) :
    C.d₁ *ᵥ h = 0 ∧ C.codiff₀ *ᵥ h = 0 :=
  ⟨((C.mem_harmonic_iff h).mp hh).2, ((C.mem_harmonic_iff h).mp hh).1⟩

/-- [proved-derived; formal-checked] **No potential reproduces this harmonic standing.** A
harmonic field that is a gradient is zero, so a nonzero mode is carried by its cohomology class
relative to the declared node/cell receivers. -/
theorem dormant_mode_is_not_a_potential {h : Fin q → ℚ} (hh : h ∈ C.harmonic)
    (φ : Fin p → ℚ) (hφ : C.d₀ *ᵥ φ = h) : h = 0 := by
  have hexact : h ∈ C.exactPart := (C.mem_exactPart_iff h).mpr ⟨φ, hφ⟩
  exact (Submodule.disjoint_def.mp C.disjoint_exact_harmonic) h hexact hh

/-- [proved-derived; formal-checked] **A closed field retains a unique harmonic representative.**
Every cocycle has one and only one harmonic mode whose difference from the field is exact. The
uniqueness is in the cohomology class; the harmonic subspace itself may have any finite dimension. -/
theorem closed_field_retains_unique_harmonic_mode {z : Fin q → ℚ} (hz : z ∈ C.cocycles) :
    ∃! h, h ∈ C.harmonic ∧ z - h ∈ C.exactPart := by
  obtain ⟨h, hh, hd⟩ := C.harmonic_meets_every_class hz
  refine ⟨h, ⟨hh, hd⟩, ?_⟩
  intro hmode hmode_prop
  have hdiff : hmode - h ∈ C.exactPart := by
    have hdiff' : hmode - h = (z - h) - (z - hmode) := by ring
    rw [hdiff']
    exact C.exactPart.sub_mem hd hmode_prop.2
  exact C.harmonic_representative_unique hmode_prop.1 hh hdiff

end Hodge

end Holonics.Transport.CellHolonomy
