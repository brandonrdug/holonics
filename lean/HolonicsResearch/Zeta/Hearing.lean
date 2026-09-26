import Mathlib
import HolonicsResearch.Zeta.DeBruijnSeal
import HolonicsResearch.Zeta.HeatKernelPhi

/-!
# The ear's threshold is the least sharpening

At seam time `τ` the flowed completed zeta is the Gaussian-weighted superposition of scale shifts
`heatE (−τ) ξ (s) = ∫ e^{τu²} Φ(u) e^{(s−½)u} du` (`HeatKernelPhi.heatE_riemannXi`). Read as the
symbol of an operator in the scale derivative `∂_c`, `τ > 0` sharpens the ear and `τ < 0` blurs
it. The threshold `Λ_DN` of `DeBruijnSeal` is the least sharpening at which the ear hears no zero
on any vertical line off the seam.

- **Symbol level** [proved-derived; formal-checked]: `Λ_DN` is the least `τ` such that for every
  real `c ≠ ½` the flowed function has no zero on `Re s = c`
  (`threshold_eq_sharpenedHearingInf`). The quantifier ranges over all real `c`: the flowed zeros
  leave the critical strip.
- **Truncation level** [proved-derived; formal-checked]: in every unital C⋆-algebra, the
  continuous functional calculus of a continuous symbol `F` at a normal element whose spectrum is
  the vertical segment `c + i[−T, T]` is invertible exactly when `F` has no zero on the segment
  (`isUnit_cfc_iff_segmentZeroFree`). The spectral truncation of `∂_c` is modelled by the
  coordinate `y ↦ c + iy` of `C([−T, T], ℂ)`, whose spectrum is that segment. With it,
  quasi-invertibility (every truncation invertible) is equivalent to having no zero on the line
  (`quasiInvertible_iff_verticalZeroFree`, Herichi–Lapidus's argument), and the threshold is the
  least sharpening at which every off-seam `F(∂_c)` is quasi-invertible
  (`threshold_eq_quasiInvertibleInf`).
- [open; #62] The unbounded operator `∂_c` on `L²(ℝ, e^{−2cx}dx)`, its normality, the
  Mellin–Plancherel unitary carrying it to multiplication by `c + iy` on `L²(ℝ, dy)`, the
  identification of its spectral truncations with the coordinate model, and the Bochner identity
  `F(∂_c) = ∫ e^{τu²}Φ(u) e^{(∂_c−½)u} du` are not constructed. Mathlib has the continuous
  functional calculus for bounded normal elements only.
-/

noncomputable section

namespace Holonics.Zeta.Hearing

open Complex Set
open Holonics.Zeta.HeatFlowEntire
open Holonics.Zeta.RiemannXi
open Holonics.Zeta.RealZeroTimes
open Holonics.Zeta.DeBruijnSeal

/-! ## Symbol level -/

/-- The flowed function at seam time `τ` has no zero on the vertical line `Re s = c`. -/
def VerticalZeroFree (τ c : ℝ) : Prop := ∀ y : ℝ, heatE (-τ) riemannXi (c + y * I) ≠ 0

/-- The sharpenings at which the ear hears no zero on any vertical line off the seam. -/
def sharpenedHearingTimes : Set ℝ := {τ | ∀ c : ℝ, c ≠ 1 / 2 → VerticalZeroFree τ c}

/-- **The hearing times are the seam times.** -/
theorem sharpenedHearingTimes_eq_seamTimes : sharpenedHearingTimes = seamTimes := by
  ext τ
  simp only [sharpenedHearingTimes, seamTimes, mem_ofPred_eq, VerticalZeroFree]
  constructor
  · intro h z hz
    by_contra hre
    apply h z.re hre z.im
    rw [re_add_im]
    exact hz
  · intro h c hc y hy
    have := h _ hy
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero] at this
    exact hc this

/-- **The ear's threshold is the least sharpening** [proved-derived; formal-checked]:
`Λ_DN = inf{τ : ∀ real c ≠ ½, heatE (−τ) ξ has no zero on Re s = c}`, and the infimum is attained:
the hearing times are exactly `[Λ_DN, ∞)`. -/
theorem threshold_eq_sharpenedHearingInf :
    Λ_DN = sInf sharpenedHearingTimes ∧ sharpenedHearingTimes = Ici Λ_DN := by
  rw [sharpenedHearingTimes_eq_seamTimes, seamTimes_eq_Ici, csInf_Ici]
  exact ⟨rfl, rfl⟩

/-- **The threshold is the least hearing time.** -/
theorem isLeast_sharpenedHearingTimes : IsLeast sharpenedHearingTimes Λ_DN := by
  rw [threshold_eq_sharpenedHearingInf.2]
  exact isLeast_Ici

/-! ## Truncation level -/

/-- **Spectral mapping at a vertical segment** [proved-derived; formal-checked]. In a unital
C⋆-algebra, for a normal element whose spectrum is the segment `c + i[−T, T]` and a symbol
continuous there, `F(a)` is invertible iff `F` has no zero on the segment. -/
theorem isUnit_cfc_iff_segmentZeroFree {A : Type*} [CStarAlgebra A] (F : ℂ → ℂ) (a : A)
    [IsStarNormal a] {c T : ℝ}
    (hspec : spectrum ℂ a = (fun y : ℝ => (c : ℂ) + y * I) '' Icc (-T) T)
    (hF : ContinuousOn F (spectrum ℂ a)) :
    IsUnit (cfc F a) ↔ ∀ y ∈ Icc (-T) T, F (c + y * I) ≠ 0 := by
  rw [isUnit_cfc_iff F a hF, hspec]
  constructor
  · intro h y hy
    exact h _ ⟨y, hy, rfl⟩
  · rintro h _ ⟨y, hy, rfl⟩
    exact h y hy

/-- The spectral truncation of the scale derivative at abscissa `c` and height `T`, modelled on
the Mellin side: the coordinate `y ↦ c + iy` of `C([−T, T], ℂ)`. -/
def truncatedScaleDerivative (c T : ℝ) : C(Icc (-T) T, ℂ) :=
  ⟨fun y => (c : ℂ) + (y : ℝ) * I, by fun_prop⟩

/-- Its spectrum is the vertical segment `c + i[−T, T]`. -/
theorem spectrum_truncatedScaleDerivative (c T : ℝ) :
    spectrum ℂ (truncatedScaleDerivative c T) =
      (fun y : ℝ => (c : ℂ) + y * I) '' Icc (-T) T := by
  rw [ContinuousMap.spectrum_eq_range]
  ext s
  simp only [mem_range, mem_image]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **Quasi-invertibility of `F(∂_c)`**: every spectral truncation is invertible. -/
def QuasiInvertible (F : ℂ → ℂ) (c : ℝ) : Prop :=
  ∀ T : ℝ, IsUnit (cfc F (truncatedScaleDerivative c T))

/-- **Quasi-invertibility is the absence of zeros on the line** [proved-derived; formal-checked],
Herichi–Lapidus's argument at the truncations, for any continuous symbol. -/
theorem quasiInvertible_iff_verticalZeroFree {F : ℂ → ℂ} (hF : Continuous F) (c : ℝ) :
    QuasiInvertible F c ↔ ∀ y : ℝ, F (c + y * I) ≠ 0 := by
  unfold QuasiInvertible
  have hT : ∀ T : ℝ, IsUnit (cfc F (truncatedScaleDerivative c T)) ↔
      ∀ y ∈ Icc (-T) T, F (c + y * I) ≠ 0 := fun T =>
    isUnit_cfc_iff_segmentZeroFree F _ (spectrum_truncatedScaleDerivative c T) hF.continuousOn
  simp only [hT]
  constructor
  · intro h y
    exact h |y| y ⟨neg_abs_le y, le_abs_self y⟩
  · intro h T y _
    exact h y

/-- **The threshold is the least sharpening at which every off-seam ear is quasi-invertible**
[proved-derived; formal-checked]. -/
theorem threshold_eq_quasiInvertibleInf :
    Λ_DN = sInf {τ : ℝ | ∀ c : ℝ, c ≠ 1 / 2 → QuasiInvertible (heatE (-τ) riemannXi) c} := by
  have hset : {τ : ℝ | ∀ c : ℝ, c ≠ 1 / 2 → QuasiInvertible (heatE (-τ) riemannXi) c} =
      sharpenedHearingTimes := by
    ext τ
    simp only [mem_ofPred_eq, sharpenedHearingTimes, VerticalZeroFree]
    have hcont : Continuous (heatE (-τ) riemannXi) :=
      (Holonics.Zeta.XiGrowth.differentiable_heatE_riemannXi (-τ)).continuous
    simp only [quasiInvertible_iff_verticalZeroFree hcont]
  rw [hset]
  exact threshold_eq_sharpenedHearingInf.1

end Holonics.Zeta.Hearing

#print axioms Holonics.Zeta.Hearing.threshold_eq_sharpenedHearingInf
#print axioms Holonics.Zeta.Hearing.quasiInvertible_iff_verticalZeroFree
#print axioms Holonics.Zeta.Hearing.threshold_eq_quasiInvertibleInf
