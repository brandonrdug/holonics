import ElementaryHolonics.Millennium.NavierStokesDirectionDepletionModulus
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-!
# High-vorticity amplitude returns a weight-one direction law

**[proved-derived]** Normalization is singular only at the zero-amplitude chart.  On an addressed
region where the vorticity magnitude is at least `m > 0`, ordinary spatial variation with
coefficient `L` therefore controls variation of the normalized direction with the exact quotient
`2 * m⁻¹ * L`.  The numerator and denominator remain separate occurrences: under the
Navier--Stokes parabolic rebase they have weights three and two, so their quotient has weight one.

This is the local high-vorticity half of a direction-depletion passage.  It does not assert that a
terminal high-vorticity region is connected, that its complement is negligible, or that the
resulting Hodge kernel moment is integrable in time.
-/

noncomputable section

open Real Set

namespace Soma.Holonics.Millennium.NavierStokesHighVorticityDirection

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesParabolicDirectionCurrent

/-- The source region on which normalization retains a positive amplitude witness. -/
def HighAmplitudeRegion (field : Space → Space) (m : ℝ) : Set Space :=
  {x | m ≤ ‖field x‖}

/-- Ordinary spatial variation restricted to an addressed region. -/
def HasLinearVariationOn (field : Space → Space) (region : Set Space) (L : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ region → ∀ ⦃y⦄, y ∈ region → ‖field x - field y‖ ≤ L * ‖x - y‖

/-- Direction coherence restricted to an addressed region. -/
def HasLinearDirectionCoherenceOn
    (field : Space → Space) (region : Set Space) (K : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ region → ∀ ⦃y⦄, y ∈ region →
    ‖normalizedDirectionSeam (field x) (field y)‖ ≤ K * ‖x - y‖

/-- Away from the zero-amplitude chart, normalization is exactly `2/m`-Lipschitz.  The two terms
record displacement of the vector and displacement of its amplitude, respectively. -/
theorem norm_normalizedDirection_sub_le
    {m : ℝ} (hm : 0 < m) {u v : Space}
    (hu : m ≤ ‖u‖) (hv : m ≤ ‖v‖) :
    ‖normalizedDirection u - normalizedDirection v‖ ≤
      (2 * m⁻¹) * ‖u - v‖ := by
  have hunorm : 0 < ‖u‖ := hm.trans_le hu
  have hvnorm : 0 < ‖v‖ := hm.trans_le hv
  have hinv : ‖u‖⁻¹ ≤ m⁻¹ := (inv_le_inv₀ hunorm hm).2 hu
  have hdecomp :
      normalizedDirection u - normalizedDirection v =
        ‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v := by
    unfold normalizedDirection
    module
  calc
    ‖normalizedDirection u - normalizedDirection v‖ ≤
        ‖‖u‖⁻¹ • (u - v)‖ + ‖(‖u‖⁻¹ - ‖v‖⁻¹) • v‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    _ = ‖u‖⁻¹ * ‖u - v‖ + |‖u‖⁻¹ - ‖v‖⁻¹| * ‖v‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hunorm)]
    _ = ‖u‖⁻¹ * ‖u - v‖ + |‖v‖ - ‖u‖| * ‖u‖⁻¹ := by
      congr 1
      have hinvdiff :
          ‖u‖⁻¹ - ‖v‖⁻¹ = (‖v‖ - ‖u‖) / (‖u‖ * ‖v‖) := by
        field_simp [hunorm.ne', hvnorm.ne']
      rw [hinvdiff, abs_div, abs_mul, abs_of_pos hunorm, abs_of_pos hvnorm]
      field_simp [hunorm.ne', hvnorm.ne']
    _ ≤ m⁻¹ * ‖u - v‖ + ‖u - v‖ * m⁻¹ := by
      gcongr
      · simpa [norm_sub_rev] using abs_norm_sub_norm_le v u
    _ = (2 * m⁻¹) * ‖u - v‖ := by ring

/-- The cross seam of two nonzero normalized directions is no larger than their direction
difference. -/
theorem norm_normalizedDirectionSeam_le_directionDifference
    {u v : Space} (hu : u ≠ 0) :
    ‖normalizedDirectionSeam u v‖ ≤
      ‖normalizedDirection v - normalizedDirection u‖ := by
  have hcross :
      cross (normalizedDirection u) (normalizedDirection v) =
        cross (normalizedDirection u)
          (normalizedDirection v - normalizedDirection u) := by
    ext component
    fin_cases component <;>
      simp [cross, crossProduct] <;> ring
  rw [normalizedDirectionSeam, hcross]
  change
    ‖WithLp.toLp 2
        (crossProduct (fun i => normalizedDirection u i)
          (fun i => (normalizedDirection v - normalizedDirection u) i))‖ ≤ _
  rw [InnerProductGeometry.norm_toLp_symm_crossProduct]
  have hright :
      WithLp.toLp 2 (fun i => (normalizedDirection v - normalizedDirection u) i) =
        normalizedDirection v - normalizedDirection u := by
    ext i
    rfl
  rw [hright]
  have hunit : ‖normalizedDirection u‖ = 1 := by
    simpa [normalizedDirection, NormedSpace.normalize] using
      (NormedSpace.norm_normalize hu)
  have hsin : Real.sin
      (InnerProductGeometry.angle (normalizedDirection u)
        (normalizedDirection v - normalizedDirection u)) ≤ 1 :=
    Real.sin_le_one _
  simpa [hunit] using
    mul_le_mul_of_nonneg_left hsin (norm_nonneg (normalizedDirection v - normalizedDirection u))

/-- A lower amplitude witness and ordinary variation derive the direction law on any common
addressed region. -/
theorem hasLinearDirectionCoherenceOn_of_lowerBound
    {field : Space → Space} {region : Set Space} {m L : ℝ} (hm : 0 < m)
    (hlower : ∀ ⦃x⦄, x ∈ region → m ≤ ‖field x‖)
    (hvariation : HasLinearVariationOn field region L) :
    HasLinearDirectionCoherenceOn field region (2 * m⁻¹ * L) := by
  intro x hx y hy
  have hxnorm : m ≤ ‖field x‖ := hlower hx
  have hynorm : m ≤ ‖field y‖ := hlower hy
  have hxzero : field x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hm.trans_le hxnorm))
  calc
    ‖normalizedDirectionSeam (field x) (field y)‖ ≤
        ‖normalizedDirection (field y) - normalizedDirection (field x)‖ :=
      norm_normalizedDirectionSeam_le_directionDifference hxzero
    _ = ‖normalizedDirection (field x) - normalizedDirection (field y)‖ := by
      rw [norm_sub_rev]
    _ ≤ (2 * m⁻¹) * ‖field x - field y‖ :=
      norm_normalizedDirection_sub_le hm hxnorm hynorm
    _ ≤ (2 * m⁻¹) * (L * ‖x - y‖) := by
      exact mul_le_mul_of_nonneg_left (hvariation hx hy)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hm.le))
    _ = (2 * m⁻¹ * L) * ‖x - y‖ := by ring

/-- A lower amplitude bound and ordinary variation derive the direction law on the same region.
The quotient `L/m`, rather than `L` alone, is the exact scale-improving carrier. -/
theorem hasLinearDirectionCoherenceOn_of_highAmplitude
    {field : Space → Space} {m L : ℝ} (hm : 0 < m)
    (hvariation : HasLinearVariationOn field (HighAmplitudeRegion field m) L) :
    HasLinearDirectionCoherenceOn field (HighAmplitudeRegion field m) (2 * m⁻¹ * L) :=
  hasLinearDirectionCoherenceOn_of_lowerBound hm (fun {_x} hx ↦ hx) hvariation

/-- The Euclidean cross interaction is bounded by the product of its two amplitude faces. -/
theorem norm_cross_le_norm_mul_norm (u v : Space) :
    ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  change
    ‖WithLp.toLp 2
        (crossProduct (fun i => u i) (fun i => v i))‖ ≤ ‖u‖ * ‖v‖
  rw [InnerProductGeometry.norm_toLp_symm_crossProduct]
  exact mul_le_of_le_one_right
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sin_le_one _)

/-- The restricted real direction law controls the complex receiver on the same addressed pair. -/
theorem complexVectorL1_receiverCrossDifference_le_of_coherenceOn
    {field : Space → Space} {region : Set Space} {K : ℝ}
    (hcoherence : HasLinearDirectionCoherenceOn field region K)
    {x : Space} (hx : x ∈ region) {y : Space} (hy : y ∈ region) :
    complexVectorL1
        (receiverCrossDifference (complexOfRealSpace (field x))
          (complexOfRealSpace (field y))) ≤
      3 * ((‖field x‖ * ‖field y‖) * (K * ‖x - y‖)) := by
  rw [receiverCrossDifference_complexOfRealSpace]
  calc
    complexVectorL1 (complexOfRealSpace (cross (field x) (field y))) ≤
        3 * ‖cross (field x) (field y)‖ :=
      complexVectorL1_complexOfRealSpace_le_three_norm _
    _ ≤ 3 * ((‖field x‖ * ‖field y‖) * (K * ‖x - y‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [cross_eq_norm_mul_normalizedDirectionSeam, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hcoherence hx hy)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The high/low split retains both alternatives in one continuous Hodge modulus: a source in the
high region is controlled by its direction seam; a source outside it is controlled by the explicit
amplitude threshold. -/
def highLowVorticityModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (K m : ℝ) : C(SpatialTorus, ℝ) where
  toFun y :=
    K * ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0 + m
  continuous_toFun := by fun_prop

theorem highLowVorticityModulus_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q y : SpatialTorus) {K m : ℝ}
    (hK : 0 ≤ K) (hm : 0 ≤ m) :
    0 ≤ highLowVorticityModulus solution t q K m y :=
  add_nonneg (mul_nonneg (mul_nonneg hK (norm_nonneg _)) dist_nonneg) hm

/-- **Exact high/low gluing at one physical receiver.**  If the receiving vorticity lies in the
high-amplitude region, every translated source is covered: high sources use the normalized
direction law, while low sources return the threshold term.  The alternatives are not erased;
they are the two summands of `highLowVorticityModulus`. -/
theorem openPeriodic_receiverCrossDifference_le_highLow
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hreceiver : m ≤ ‖torusVorticityEvolution solution t q‖)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L)
    (y : SpatialTorus) :
    complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y))) ≤
      (9 * ‖torusVorticityEvolution solution t q‖) *
        highLowVorticityModulus solution t q (2 * m⁻¹ * L) m y := by
  let field : Space → Space := fun x ↦ vorticityField velocity x t.1
  let x : Space := centeredEuclideanRepresentative q
  let displacement : Space := centeredEuclideanRepresentative y
  have hxProjection : euclideanToSpatialTorus x = q :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative q
  have hdisplacementProjection : euclideanToSpatialTorus displacement = y :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative y
  have hxsubProjection : euclideanToSpatialTorus (x - displacement) = q - y := by
    rw [euclideanToSpatialTorus_sub, hxProjection, hdisplacementProjection]
  have hxfield : field x = torusVorticityEvolution solution t q := by
    rw [← hxProjection, torusVorticityEvolution_projection]
  have hsourcefield : field (x - displacement) =
      torusVorticityEvolution solution t (q - y) := by
    rw [← hxsubProjection, torusVorticityEvolution_projection]
  have hxhigh : x ∈ HighAmplitudeRegion field m := by
    simpa [HighAmplitudeRegion, hxfield] using hreceiver
  have hxnorm : ‖x‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves q
  have hdisplacementNorm : ‖displacement‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves y
  have hxmem : x ∈ Metric.closedBall (0 : Space) 3 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxnorm.trans (by norm_num)
  have hxsubmem : x - displacement ∈ Metric.closedBall (0 : Space) 3 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le x displacement).trans (by linarith)
  have hcoherence := hasLinearDirectionCoherenceOn_of_lowerBound hm
    (fun {_z} hz ↦ hz.1) hvariation
  have hdisplacement : ‖displacement‖ ≤ 3 * dist y 0 :=
    norm_centeredEuclideanRepresentative_le_three_mul_dist y
  have hcoefficient : 0 ≤ 2 * m⁻¹ * L :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hm.le)) hL
  by_cases hsourceHigh :
      m ≤ ‖torusVorticityEvolution solution t (q - y)‖
  · have hysourceHigh : x - displacement ∈ HighAmplitudeRegion field m := by
      simpa [HighAmplitudeRegion, hsourcefield] using hsourceHigh
    have hxregion : x ∈ HighAmplitudeRegion field m ∩ Metric.closedBall 0 3 :=
      ⟨hxhigh, hxmem⟩
    have hysource :
        x - displacement ∈ HighAmplitudeRegion field m ∩ Metric.closedBall 0 3 :=
      ⟨hysourceHigh, hxsubmem⟩
    have hcross := complexVectorL1_receiverCrossDifference_le_of_coherenceOn
      hcoherence hxregion hysource
    have hleft : x - (x - displacement) = displacement := by abel
    have hxfield' :
        vorticityField velocity x t.1 = torusVorticityEvolution solution t q := by
      simpa [field] using hxfield
    have hsourcefield' :
        vorticityField velocity (x - displacement) t.1 =
          torusVorticityEvolution solution t (q - y) := by
      simpa [field] using hsourcefield
    rw [hleft, hxfield', hsourcefield'] at hcross
    change
      complexVectorL1
          (receiverCrossDifference
            (complexOfRealSpace (torusVorticityEvolution solution t q))
            (complexOfRealSpace (torusVorticityEvolution solution t (q - y)))) ≤ _
    calc
      complexVectorL1
          (receiverCrossDifference
            (complexOfRealSpace (torusVorticityEvolution solution t q))
            (complexOfRealSpace (torusVorticityEvolution solution t (q - y)))) ≤
        3 * ((‖torusVorticityEvolution solution t q‖ *
          ‖torusVorticityEvolution solution t (q - y)‖) *
            ((2 * m⁻¹ * L) * ‖displacement‖)) := hcross
      _ ≤ 3 * ((‖torusVorticityEvolution solution t q‖ *
          ‖torusVorticityEvolution solution t (q - y)‖) *
            ((2 * m⁻¹ * L) * (3 * dist y 0))) := by gcongr
      _ ≤ (9 * ‖torusVorticityEvolution solution t q‖) *
          ((2 * m⁻¹ * L) * ‖torusVorticityEvolution solution t (q - y)‖ *
            dist y 0 + m) := by
        have hmnonneg : 0 ≤ m := hm.le
        nlinarith [norm_nonneg (torusVorticityEvolution solution t q),
          norm_nonneg (torusVorticityEvolution solution t (q - y)),
          (show 0 ≤ dist y 0 from dist_nonneg)]
      _ = (9 * ‖torusVorticityEvolution solution t q‖) *
          highLowVorticityModulus solution t q (2 * m⁻¹ * L) m y := by
        rfl

  · have hsourcelow :
        ‖torusVorticityEvolution solution t (q - y)‖ ≤ m :=
      le_of_lt (lt_of_not_ge hsourceHigh)
    change
      complexVectorL1
          (receiverCrossDifference
            (complexOfRealSpace (torusVorticityEvolution solution t q))
            (complexOfRealSpace (torusVorticityEvolution solution t (q - y)))) ≤ _
    rw [receiverCrossDifference_complexOfRealSpace]
    calc
      complexVectorL1
          (complexOfRealSpace
            (cross (torusVorticityEvolution solution t q)
              (torusVorticityEvolution solution t (q - y)))) ≤
        3 * ‖cross (torusVorticityEvolution solution t q)
          (torusVorticityEvolution solution t (q - y))‖ :=
        complexVectorL1_complexOfRealSpace_le_three_norm _
      _ ≤ 3 * (‖torusVorticityEvolution solution t q‖ *
          ‖torusVorticityEvolution solution t (q - y)‖) := by
        exact mul_le_mul_of_nonneg_left (norm_cross_le_norm_mul_norm _ _) (by norm_num)
      _ ≤ 3 * (‖torusVorticityEvolution solution t q‖ * m) := by gcongr
      _ ≤ (9 * ‖torusVorticityEvolution solution t q‖) *
          ((2 * m⁻¹ * L) * ‖torusVorticityEvolution solution t (q - y)‖ *
            dist y 0 + m) := by
        have hreceiverThreshold :
            0 ≤ ‖torusVorticityEvolution solution t q‖ * m :=
          mul_nonneg (norm_nonneg _) hm.le
        have hdirectionTerm :
            0 ≤ (2 * m⁻¹ * L) *
              ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0 :=
          mul_nonneg (mul_nonneg hcoefficient (norm_nonneg _)) dist_nonneg
        calc
          3 * (‖torusVorticityEvolution solution t q‖ * m) ≤
              9 * (‖torusVorticityEvolution solution t q‖ * m) :=
            mul_le_mul_of_nonneg_right (by norm_num) hreceiverThreshold
          _ = (9 * ‖torusVorticityEvolution solution t q‖) * m := by ring
          _ ≤ (9 * ‖torusVorticityEvolution solution t q‖) *
              ((2 * m⁻¹ * L) *
                ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0 + m) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hdirectionTerm)
              (mul_nonneg (by norm_num) (norm_nonneg _))
      _ = (9 * ‖torusVorticityEvolution solution t q‖) *
          highLowVorticityModulus solution t q (2 * m⁻¹ * L) m y := by
        rfl

/-- The high/low gluing is a complete inhabitant of the existing physical Hodge-modulus port. -/
def openPeriodicHighLowDirectionModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hreceiver : m ≤ ‖torusVorticityEvolution solution t q‖)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L) :
    OpenPeriodicSpatialCrossModulus solution t q where
  modulus := highLowVorticityModulus solution t q (2 * m⁻¹ * L) m
  constant := 9 * ‖torusVorticityEvolution solution t q‖
  constant_nonneg := mul_nonneg (by norm_num) (norm_nonneg _)
  modulus_nonneg := fun y ↦ highLowVorticityModulus_nonneg solution t q y
    (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hm.le)) hL) hm.le
  cross_le := openPeriodic_receiverCrossDifference_le_highLow
    solution t q hm hL hreceiver hvariation

/-- Every exact dyadic Hodge scale now receives the glued high/low source population.  What
remains is the scale-uniform spacetime control of this explicitly displayed kernel moment. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_highLowMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hreceiver : m ≤ ‖torusVorticityEvolution solution t q‖)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L)
    (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      (9 * ‖torusVorticityEvolution solution t q‖) *
        dyadicHodgeJacobianKernelModulusMoment
          (highLowVorticityModulus solution t q (2 * m⁻¹ * L) m) scale := by
  exact openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
    solution t q
      (openPeriodicHighLowDirectionModulus
        solution t q hm hL hreceiver hvariation) scale

/-- The symmetric glued modulus.  Its first summand is the high/high direction interaction.  Its
second summand retains the two distinct low-amplitude alternatives, so neither endpoint is chosen
as a privileged receiver by the carrier itself. -/
def symmetricHighLowVorticityModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (K m : ℝ) : C(SpatialTorus, ℝ) where
  toFun y :=
    K * ‖torusVorticityEvolution solution t q‖ *
        ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0 +
      m * (‖torusVorticityEvolution solution t q‖ +
        ‖torusVorticityEvolution solution t (q - y)‖)
  continuous_toFun := by fun_prop

theorem symmetricHighLowVorticityModulus_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q y : SpatialTorus) {K m : ℝ}
    (hK : 0 ≤ K) (hm : 0 ≤ m) :
    0 ≤ symmetricHighLowVorticityModulus solution t q K m y :=
  add_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg hK (norm_nonneg _)) (norm_nonneg _)) dist_nonneg)
    (mul_nonneg hm (add_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- **Receiver-symmetric high/low gluing.**  Every pair of physical vorticity occurrences is
covered.  The high/high branch uses the derived normalized-direction law; if either endpoint is
low, that endpoint's amplitude threshold controls the cross interaction. -/
theorem openPeriodic_receiverCrossDifference_le_symmetricHighLow
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L)
    (y : SpatialTorus) :
    complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y))) ≤
      9 * symmetricHighLowVorticityModulus
        solution t q (2 * m⁻¹ * L) m y := by
  have hcoefficient : 0 ≤ 2 * m⁻¹ * L :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hm.le)) hL
  by_cases hreceiverHigh : m ≤ ‖torusVorticityEvolution solution t q‖
  · have hcross := openPeriodic_receiverCrossDifference_le_highLow
      solution t q hm hL hreceiverHigh hvariation y
    calc
      complexVectorL1
          (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
            (complexTorusVorticitySlice solution t (q - y))) ≤
        (9 * ‖torusVorticityEvolution solution t q‖) *
          highLowVorticityModulus solution t q (2 * m⁻¹ * L) m y := hcross
      _ ≤ 9 * symmetricHighLowVorticityModulus
          solution t q (2 * m⁻¹ * L) m y := by
        have hextra :
            0 ≤ m * ‖torusVorticityEvolution solution t (q - y)‖ :=
          mul_nonneg hm.le (norm_nonneg _)
        simp only [highLowVorticityModulus, symmetricHighLowVorticityModulus,
          ContinuousMap.coe_mk]
        nlinarith
  · have hreceiverLow : ‖torusVorticityEvolution solution t q‖ ≤ m :=
      le_of_lt (lt_of_not_ge hreceiverHigh)
    change
      complexVectorL1
          (receiverCrossDifference
            (complexOfRealSpace (torusVorticityEvolution solution t q))
            (complexOfRealSpace (torusVorticityEvolution solution t (q - y)))) ≤ _
    rw [receiverCrossDifference_complexOfRealSpace]
    calc
      complexVectorL1
          (complexOfRealSpace
            (cross (torusVorticityEvolution solution t q)
              (torusVorticityEvolution solution t (q - y)))) ≤
        3 * ‖cross (torusVorticityEvolution solution t q)
          (torusVorticityEvolution solution t (q - y))‖ :=
        complexVectorL1_complexOfRealSpace_le_three_norm _
      _ ≤ 3 * (‖torusVorticityEvolution solution t q‖ *
          ‖torusVorticityEvolution solution t (q - y)‖) := by
        exact mul_le_mul_of_nonneg_left (norm_cross_le_norm_mul_norm _ _) (by norm_num)
      _ ≤ 3 * (m * ‖torusVorticityEvolution solution t (q - y)‖) := by gcongr
      _ ≤ 9 * symmetricHighLowVorticityModulus
          solution t q (2 * m⁻¹ * L) m y := by
        have hreceiverTerm :
            0 ≤ m * ‖torusVorticityEvolution solution t q‖ :=
          mul_nonneg hm.le (norm_nonneg _)
        have hsourceTerm :
            0 ≤ m * ‖torusVorticityEvolution solution t (q - y)‖ :=
          mul_nonneg hm.le (norm_nonneg _)
        have hdirectionTerm :
            0 ≤ (2 * m⁻¹ * L) * ‖torusVorticityEvolution solution t q‖ *
              ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0 :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg hcoefficient (norm_nonneg _)) (norm_nonneg _)) dist_nonneg
        simp only [symmetricHighLowVorticityModulus, ContinuousMap.coe_mk]
        nlinarith

/-- The symmetric gluing removes the high-receiver hypothesis from the physical Hodge port. -/
def openPeriodicSymmetricHighLowDirectionModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L) :
    OpenPeriodicSpatialCrossModulus solution t q where
  modulus := symmetricHighLowVorticityModulus solution t q (2 * m⁻¹ * L) m
  constant := 9
  constant_nonneg := by norm_num
  modulus_nonneg := fun y ↦ symmetricHighLowVorticityModulus_nonneg solution t q y
    (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hm.le)) hL) hm.le
  cross_le := openPeriodic_receiverCrossDifference_le_symmetricHighLow
    solution t q hm hL hvariation

/-- The receiver-symmetric high/low population enters every exact dyadic Hodge scale. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_symmetricHighLowMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {m L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hvariation : HasLinearVariationOn
      (fun x ↦ vorticityField velocity x t.1)
      (HighAmplitudeRegion (fun x ↦ vorticityField velocity x t.1) m ∩
        Metric.closedBall 0 3) L)
    (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      9 * dyadicHodgeJacobianKernelModulusMoment
        (symmetricHighLowVorticityModulus solution t q (2 * m⁻¹ * L) m) scale := by
  exact openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
    solution t q
      (openPeriodicSymmetricHighLowDirectionModulus
        solution t q hm hL hvariation) scale

/-- The amplitude/variation quotient has exact parabolic weight one: a weight-three numerator
divided by a weight-two lower-amplitude occurrence. -/
theorem parabolic_directionCoefficient_eq
    {scale m L : ℝ} (hscale : 0 < scale) (hm : 0 < m) :
    2 * (scale ^ 2 * m)⁻¹ * (scale ^ 3 * L) =
      scale * (2 * m⁻¹ * L) := by
  field_simp [hscale.ne', hm.ne']

section Audit

#print axioms norm_normalizedDirection_sub_le
#print axioms norm_normalizedDirectionSeam_le_directionDifference
#print axioms hasLinearDirectionCoherenceOn_of_highAmplitude
#print axioms norm_cross_le_norm_mul_norm
#print axioms complexVectorL1_receiverCrossDifference_le_of_coherenceOn
#print axioms highLowVorticityModulus_nonneg
#print axioms openPeriodic_receiverCrossDifference_le_highLow
#print axioms openPeriodicHighLowDirectionModulus
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_highLowMoment
#print axioms symmetricHighLowVorticityModulus_nonneg
#print axioms openPeriodic_receiverCrossDifference_le_symmetricHighLow
#print axioms openPeriodicSymmetricHighLowDirectionModulus
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_symmetricHighLowMoment
#print axioms parabolic_directionCoefficient_eq

end Audit

end Soma.Holonics.Millennium.NavierStokesHighVorticityDirection
