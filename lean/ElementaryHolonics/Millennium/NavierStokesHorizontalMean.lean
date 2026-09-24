import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import ElementaryHolonics.Millennium.NavierStokesCompactSlabBound

/-!
# Actual horizontal averaging

The mean is taken over the literal horizontal square `[0,1] × [0,1]` at fixed vertical
coordinate. The two integrals are joined before differentiating. Compact-slab bounds pay the
actual local domination, retaining the derivative of the complete horizontal population.
-/

noncomputable section

open ContDiff Set MeasureTheory Filter
open scoped Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesHorizontalMean

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesCompactSlabBound

def horizontalMean (f : Space → ℝ) (z : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (assemble x y z)

def horizontalMeanIntegrand (f : Space → ℝ) (x y z : ℝ) : ℝ :=
  f (assemble x y z)

theorem horizontalMeanIntegrand_hasDerivAt
    (f : Space → ℝ) (hf : ContDiff ℝ 1 f) (x y z : ℝ) :
    HasDerivAt (fun ζ ↦ horizontalMeanIntegrand f x y ζ)
      (fderiv ℝ f (assemble x y z) (EuclideanSpace.single (2 : Fin 3) 1)) z := by
  have hline : HasDerivAt (fun ζ : ℝ ↦ assemble x y ζ)
      (EuclideanSpace.single (2 : Fin 3) 1) z := by
    convert (hasDerivAt_const z (assemble x y 0)).add
      ((hasDerivAt_id z).smul_const (EuclideanSpace.single (2 : Fin 3) 1)) using 1 <;> try rfl
    funext ζ
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [assemble]
    simp
  exact (hf.differentiable (by norm_num) (assemble x y z)).hasFDerivAt.comp_hasDerivAt z hline

theorem horizontalMean_def (f : Space → ℝ) (z : ℝ) :
    horizontalMean f z = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      horizontalMeanIntegrand f x y z := rfl

def horizontalSquare : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

def squareMean (f : Space → ℝ) (z : ℝ) : ℝ :=
  ∫ p in horizontalSquare, f (assemble p.1 p.2 z)

theorem horizontalSquare_compact : IsCompact horizontalSquare := isCompact_Icc.prod isCompact_Icc

theorem continuous_horizontalSample (f : Space → ℝ) (hf : Continuous f) (z : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ f (assemble p.1 p.2 z)) :=
  hf.comp (by unfold assemble; fun_prop)

theorem horizontalMean_eq_squareMean (f : Space → ℝ) (hf : Continuous f) (z : ℝ) :
    horizontalMean f z = squareMean f z := by
  have hi : IntegrableOn (fun p : ℝ × ℝ ↦ f (assemble p.1 p.2 z)) horizontalSquare :=
    ContinuousOn.integrableOn_compact horizontalSquare_compact
      (continuous_horizontalSample f hf z).continuousOn
  have hsplit : (∫ p in horizontalSquare, f (assemble p.1 p.2 z)) =
      ∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1, f (assemble x y z) := by
    rw [Measure.volume_eq_prod] at hi ⊢
    exact setIntegral_prod _ hi
  simpa only [horizontalMean, squareMean, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hsplit.symm

theorem horizontalMean_continuous (f : Space → ℝ) (hf : Continuous f) :
    Continuous (horizontalMean f) := by
  have hc : Continuous (fun q : ℝ × (ℝ × ℝ) ↦ f (assemble q.2.1 q.2.2 q.1)) :=
    hf.comp (by unfold assemble; fun_prop)
  have h := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun z (p : ℝ × ℝ) ↦ f (assemble p.1 p.2 z)) hc horizontalSquare_compact
  have heq : horizontalMean f = squareMean f := funext (horizontalMean_eq_squareMean f hf)
  rw [heq]
  exact h

theorem horizontalMean_add (f g : Space → ℝ) (hf : Continuous f) (hg : Continuous g)
    (z : ℝ) :
    horizontalMean (fun p ↦ f p + g p) z = horizontalMean f z + horizontalMean g z := by
  rw [horizontalMean_eq_squareMean (fun p ↦ f p + g p) (hf.add hg), horizontalMean_eq_squareMean f hf,
    horizontalMean_eq_squareMean g hg]
  exact integral_add
    (ContinuousOn.integrableOn_compact horizontalSquare_compact
      (continuous_horizontalSample f hf z).continuousOn)
    (ContinuousOn.integrableOn_compact horizontalSquare_compact
      (continuous_horizontalSample g hg z).continuousOn)

theorem axialDerivativeField_continuous (f : Space → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (fun p : Space ↦ fderiv ℝ f p (EuclideanSpace.single (2 : Fin 3) 1)) :=
  (hf.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)

/-- The mean derivative follows from the complete compact-slab bound and an actual integral
interchange. The bound is local in the axial parameter and need not be uniform in fluid time. -/
theorem horizontalMean_hasDerivAt (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (z0 : ℝ) :
    HasDerivAt (horizontalMean f)
      (horizontalMean (fun p ↦ fderiv ℝ f p (EuclideanSpace.single (2 : Fin 3) 1)) z0) z0 := by
  let df : Space → ℝ := fun p ↦ fderiv ℝ f p (EuclideanSpace.single (2 : Fin 3) 1)
  have hdf : Continuous df := axialDerivativeField_continuous f hf
  let F : ℝ → ℝ × ℝ → ℝ := fun z p ↦ f (assemble p.1 p.2 z)
  let F' : ℝ → ℝ × ℝ → ℝ := fun z p ↦ df (assemble p.1 p.2 z)
  let mu : Measure (ℝ × ℝ) := volume.restrict horizontalSquare
  have hF (z : ℝ) : Continuous (F z) := continuous_horizontalSample f hf.continuous z
  have hF' (z : ℝ) : Continuous (F' z) := continuous_horizontalSample df hdf z
  obtain ⟨M, hMpos, hM⟩ := exists_compact_slab_fderiv_bound f hf z0
  have hs : Ioo (z0 - 1) (z0 + 1) ∈ 𝓝 z0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ z in 𝓝 z0, AEStronglyMeasurable (F z) mu :=
    Filter.Eventually.of_forall (fun z ↦ (hF z).aestronglyMeasurable)
  have hint : Integrable (F z0) mu :=
    ContinuousOn.integrableOn_compact horizontalSquare_compact (hF z0).continuousOn
  have hbound : ∀ᵐ p ∂mu, ∀ z ∈ Ioo (z0 - 1) (z0 + 1), ‖F' z p‖ ≤ M := by
    filter_upwards [ae_restrict_mem horizontalSquare_compact.measurableSet] with p hp
    intro z hz
    simpa only [F', df, Real.norm_eq_abs] using
      hM p.1 hp.1 p.2 hp.2 z ⟨hz.1.le, hz.2.le⟩
  have hMint : Integrable (fun _ : ℝ × ℝ ↦ M) mu :=
    ContinuousOn.integrableOn_compact horizontalSquare_compact continuous_const.continuousOn
  have hderiv : ∀ᵐ p ∂mu, ∀ z ∈ Ioo (z0 - 1) (z0 + 1),
      HasDerivAt (fun z ↦ F z p) (F' z p) z := by
    filter_upwards [] with p
    intro z _
    exact horizontalMeanIntegrand_hasDerivAt f (hf.of_le (by norm_num)) p.1 p.2 z
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := mu)
    (F := F) (F' := F') (bound := fun _ ↦ M) hs hmeas hint
    (hF' z0).aestronglyMeasurable hbound hMint hderiv).2
  have heq : horizontalMean f = squareMean f := funext (horizontalMean_eq_squareMean f hf.continuous)
  rw [heq, horizontalMean_eq_squareMean df hdf z0]
  exact h

#print axioms horizontalMeanIntegrand_hasDerivAt
#print axioms horizontalMean_eq_squareMean
#print axioms horizontalMean_continuous
#print axioms horizontalMean_hasDerivAt

end Soma.Holonics.Millennium.NavierStokesHorizontalMean
