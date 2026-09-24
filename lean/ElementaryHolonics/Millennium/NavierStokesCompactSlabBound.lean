import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart

/-!
# Compact slab bounds for an actual spatial derivative

The bound is obtained from the compact assembled slab and the continuous actual fderivative
receiver.  It is a helper for differentiation under the horizontal mean integrals.
-/

noncomputable section

open ContDiff Set
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesCompactSlabBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart

def slabSet (z₀ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (z₀ - 1) (z₀ + 1))

theorem exists_compact_slab_fderiv_bound
    (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (z₀ : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ∀ z ∈ Icc (z₀ - 1) (z₀ + 1),
        |fderiv ℝ f (assemble x y z) (EuclideanSpace.single (2 : Fin 3) 1)| ≤ M := by
  let K : Set (ℝ × (ℝ × ℝ)) := slabSet z₀
  have hK : IsCompact K := by
    unfold K slabSet
    exact (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
      ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
        (isCompact_Icc : IsCompact (Icc (z₀ - 1) (z₀ + 1))))
  let receiver : (ℝ × (ℝ × ℝ)) → ℝ := fun q ↦
    fderiv ℝ f (assemble q.1 q.2.1 q.2.2)
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  have hfd : Continuous (fun p : Space × Space ↦ fderiv ℝ f p.1 p.2) :=
    hf.continuous_fderiv_apply (by norm_num)
  have hassemble : Continuous (fun q : ℝ × (ℝ × ℝ) ↦
      (assemble q.1 q.2.1 q.2.2,
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) := by
    have h0 : Continuous (fun q : ℝ × (ℝ × ℝ) ↦
        q.1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
      continuous_fst.smul continuous_const
    have h1 : Continuous (fun q : ℝ × (ℝ × ℝ) ↦
        q.2.1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) :=
      continuous_snd.fst.smul continuous_const
    have h2 : Continuous (fun q : ℝ × (ℝ × ℝ) ↦
        q.2.2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) :=
      continuous_snd.snd.smul continuous_const
    have hassemble : Continuous (fun q : ℝ × (ℝ × ℝ) ↦ assemble q.1 q.2.1 q.2.2) := by
      change Continuous (fun q : ℝ × (ℝ × ℝ) ↦
        q.1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
          q.2.1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
            q.2.2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      exact (h0.add h1).add h2
    exact hassemble.prodMk continuous_const
  have hreceiver : Continuous receiver := by
    exact hfd.comp hassemble
  obtain ⟨C : ℝ, hC⟩ := hK.exists_bound_of_continuousOn hreceiver.continuousOn
  refine ⟨|C| + 1, by linarith [abs_nonneg C], ?_⟩
  intro x hx y hy z hz
  have hxyz : (x, (y, z)) ∈ K := by
    change x ∈ Icc (0 : ℝ) 1 ∧ (y ∈ Icc (0 : ℝ) 1 ∧ z ∈ Icc (z₀ - 1) (z₀ + 1))
    exact ⟨hx, hy, hz⟩
  have hbound := hC (x, (y, z)) hxyz
  have habs : ‖receiver (x, (y, z))‖ ≤ |C| := hbound.trans (le_abs_self C)
  have hone : |C| ≤ |C| + 1 := le_add_of_nonneg_right (by norm_num)
  exact (habs.trans hone)

#print axioms exists_compact_slab_fderiv_bound

end Soma.Holonics.Millennium.NavierStokesCompactSlabBound
