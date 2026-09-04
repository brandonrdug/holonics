import ElementaryHolonics.Millennium.NavierStokesWeightedSobolevHilbert
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered

/-!
# The complete native H³ path carrier

**[proved-derived]** Local restart is a circulation over a closed time aperture, not an unrelated
population of pointwise states.  This owner installs the exact Banach carrier

`C([0,T], H³_weighted(T³; ℂ³))`

with its compact-domain supremum norm and its complete-space instance.  The canonical projection
extension to all real times is only an apparatus face for feeding interval-integral APIs; on the
declared aperture it is exactly the original path, and everywhere its norm and two-path separation
remain controlled by the same path norm.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesWeightedPathSpace

open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Continuous native weighted `H³` paths on the addressed closed restart aperture. -/
abbrev WeightedH3Path (T : ℝ) :=
  C(Icc (0 : ℝ) T, PeriodicVectorWeightedSobolev 3)

/-- Extend a path by endpoint projection.  This adds no new state: values before zero and after
`T` are the corresponding boundary values of the same continuing path. -/
def weightedPathExtension
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) :
    C(ℝ, PeriodicVectorWeightedSobolev 3) :=
  ContinuousMap.IccExtend hT path

/-- On the addressed aperture, projection extension is exactly the source path. -/
@[simp]
theorem weightedPathExtension_of_mem
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    weightedPathExtension hT path t = path ⟨t, ht⟩ := by
  simp [weightedPathExtension, ContinuousMap.IccExtend,
    Set.IccExtend, Set.projIcc, ht.1, ht.2]

/-- Every path value is bounded by the compact-domain supremum norm. -/
theorem norm_weightedPath_apply_le
    {T : ℝ} (path : WeightedH3Path T) (t : Icc (0 : ℝ) T) :
    ‖path t‖ ≤ ‖path‖ :=
  path.norm_coe_le_norm t

/-- Endpoint projection does not enlarge the path norm. -/
theorem norm_weightedPathExtension_le
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    ‖weightedPathExtension hT path t‖ ≤ ‖path‖ := by
  change ‖path (Set.projIcc 0 T hT t)‖ ≤ ‖path‖
  exact path.norm_coe_le_norm _

/-- The same projection preserves the declared two-path supremum separation. -/
theorem norm_weightedPathExtension_sub_le
    {T : ℝ} (hT : 0 ≤ T) (u v : WeightedH3Path T) (t : ℝ) :
    ‖weightedPathExtension hT u t - weightedPathExtension hT v t‖ ≤ ‖u - v‖ := by
  change ‖(u - v) (Set.projIcc 0 T hT t)‖ ≤ ‖u - v‖
  exact (u - v).norm_coe_le_norm _

section Audit

#synth NormedAddCommGroup (WeightedH3Path 1)
#synth CompleteSpace (WeightedH3Path 1)

#print axioms weightedPathExtension_of_mem
#print axioms norm_weightedPathExtension_le
#print axioms norm_weightedPathExtension_sub_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
