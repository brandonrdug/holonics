import Holonics.Geometry.HolonicTorusKnots
import Holonics.Fluid.NavierStokesTorusFourier
import Holonics.Aeon.Clock.CarryWord
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# A finite rank-one subgroup receiver on the genuine two-torus

The helical pair's two phase faces use `HolonicTorusKnots.GeometricTwoTorus`, not a
second torus model. The slope `(1,h)` is sampled through the existing injective
`ZMod.toAddCircle`. Averaging translates the field by this finite subgroup;
it does not iterate a hyperbolic torus map. Its character mask is exactly
`N ∣ k₁ + h k₂`. The Fourier receiver below is the existing probability-Haar
`UnitAddTorus.mFourierCoeff`, in the normalization of `NavierStokesTorusFourier`.

This is the Fourier/designed-placement law of U7 (#62, #386). The computational
object is the helical pair interaction: helix, pair, faces/placement and the
receiver's tube cut are touched; cell holonomy and tower restrictions stay attached.
No native periodic field, placement or decoder is declared here, and no learned
HNN behavior is inferred from a mathematical projector.

The complete dual-mode residual uses Nagel's declared tensor Sobolev weights
(https://arxiv.org/html/2502.17082v2, §1.2–1.3). Coefficient and convergence
hypotheses are explicit. Identifying the displayed piecewise quadratic physical
kernel with those coefficients is a separate analytic obligation; general
Fibonacci global optimality is not claimed. A rechart carries the kernel with
the nodes, rather than leaving an anisotropic kernel fixed.

Agent-inferred choices: a finite additive subgroup gives the reindexing law
needed for idempotence; the full character lattice keeps every alias rather than
declaring an aperture an exact quadrature rule. These choices avoid the recorded
failures of a partial source identity counted as a consuming join, a dropped
spectral residual, and formal verification counted as learned machine behavior.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Holonics.Geometry.FiniteTorusSubgroupReceiver

open Holonics.Geometry.HolonicTorusKnots
open Holonics.Fluid.NavierStokesTorusFourier

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Frequency := Fin 2 → ℤ

variable {N : ℕ} [NeZero N]

/-- The primitive helical pair slope. -/
def rankOneSlope (h : ℤ) : Fin 2 → ℤ := ![1, h]

/-- The finite subgroup's addressed nodes, using the existing geometric slope map. -/
def rankOneNodeHom (N : ℕ) [NeZero N] (h : ℤ) : ZMod N →+ GeometricTwoTorus where
  toFun m := torusSlopeMap (rankOneSlope h) (ZMod.toAddCircle m)
  map_zero' := by ext i; simp [torusSlopeMap]
  map_add' m n := by ext i; simp [torusSlopeMap]

@[simp]
theorem rankOneNodeHom_apply (h : ℤ) (m : ZMod N) (i : Fin 2) :
    rankOneNodeHom N h m i = rankOneSlope h i • ZMod.toAddCircle m := rfl

/-- The sampling chart is literally `(m/N, h*m/N)` modulo the integral lattice. -/
theorem rankOneNodeHom_intCast (h m : ℤ) :
    rankOneNodeHom N h (m : ZMod N) =
      realToTwoTorus (torusSlopeLift (rankOneSlope h) ((m : ℝ) / N)) := by
  change torusSlopeMap (rankOneSlope h) (ZMod.toAddCircle (m : ZMod N)) = _
  rw [realToTwoTorus_torusSlopeLift, ZMod.toAddCircle_intCast]

theorem rankOneNodeHom_injective (h : ℤ) :
    Function.Injective (rankOneNodeHom N h) := by
  intro m n hmn
  apply ZMod.toAddCircle_injective N
  simpa [rankOneSlope] using congrFun hmn 0

/-- The image is an actual additive subgroup of the quotient torus. -/
def rankOneSubgroup (N : ℕ) [NeZero N] (h : ℤ) : AddSubgroup GeometricTwoTorus :=
  (rankOneNodeHom N h).range

theorem card_rankOneSubgroup (h : ℤ) : Nat.card (rankOneSubgroup N h) = N := by
  change Nat.card (Set.range (rankOneNodeHom N h)) = N
  rw [Nat.card_range_of_injective (rankOneNodeHom_injective h)]
  simp

/-- Translation averaging over an addressed finite subgroup; normalization counts its nodes. -/
def subgroupAverage (node : ZMod N →+ GeometricTwoTorus)
    (f : GeometricTwoTorus → ℂ) (x : GeometricTwoTorus) : ℂ :=
  (N : ℂ)⁻¹ * ∑ m : ZMod N, f (x + node m)

/-- Translation along a subgroup node leaves its average unchanged. -/
theorem subgroupAverage_translate (node : ZMod N →+ GeometricTwoTorus)
    (f : GeometricTwoTorus → ℂ) (x : GeometricTwoTorus) (a : ZMod N) :
    subgroupAverage node f (x + node a) = subgroupAverage node f x := by
  classical
  unfold subgroupAverage
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun m ↦ by
    simp only [Equiv.coe_addRight, map_add]
    congr 1
    abel)

/-- Applying the same receiver twice makes no further change, for every field. -/
theorem subgroupAverage_idempotent (node : ZMod N →+ GeometricTwoTorus)
    (f : GeometricTwoTorus → ℂ) :
    subgroupAverage node (subgroupAverage node f) = subgroupAverage node f := by
  funext x
  change (N : ℂ)⁻¹ * (∑ m : ZMod N, subgroupAverage node f (x + node m)) = _
  simp only [subgroupAverage_translate, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_mul]

def rankOneAverage (N : ℕ) [NeZero N] (h : ℤ) :=
  subgroupAverage (rankOneNodeHom N h)

theorem rankOneAverage_idempotent (h : ℤ) (f : GeometricTwoTorus → ℂ) :
    rankOneAverage N h (rankOneAverage N h f) = rankOneAverage N h f :=
  subgroupAverage_idempotent _ _

/-- The same averaging operation as a continuous map on the existing torus. -/
def subgroupAverageMap (node : ZMod N →+ GeometricTwoTorus)
    (f : C(GeometricTwoTorus, ℂ)) : C(GeometricTwoTorus, ℂ) where
  toFun := subgroupAverage node f
  continuous_toFun := by
    unfold subgroupAverage
    fun_prop

theorem mFourier_translate (k : Frequency) (x y : GeometricTwoTorus) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

theorem fourier_zsmul (a b : ℤ) (q : UnitAddCircle) :
    fourier a (b • q) = fourier (a * b) q := by
  simp only [fourier_apply, mul_zsmul]

theorem fourier_toAddCircle (a : ℤ) (m : ZMod N) :
    fourier a (ZMod.toAddCircle m) = ZMod.stdAddChar ((a : ZMod N) * m) := by
  rw [fourier_apply, ← map_zsmul, zsmul_eq_mul]
  rfl

/-- The dual contact congruence read by the finite subgroup. -/
def dualContact (h : ℤ) (k : Frequency) : ℤ := k 0 + h * k 1

theorem mFourier_rankOneNode (h : ℤ) (k : Frequency) (m : ZMod N) :
    UnitAddTorus.mFourier k (rankOneNodeHom N h m) =
      ZMod.stdAddChar ((dualContact h k : ZMod N) * m) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    rankOneNodeHom_apply, rankOneSlope, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_zsmul, fourier_zsmul, fourier_toAddCircle]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp [dualContact]
  ring

theorem sum_stdAddChar_mul (a : ZMod N) :
    (∑ m : ZMod N, ZMod.stdAddChar (a * m)) = if a = 0 then (N : ℂ) else 0 := by
  classical
  split_ifs with ha
  · simp [ha, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)

/-- The exact character average: survival iff the complete integer contact is divisible by N. -/
theorem rankOne_character_average (h : ℤ) (k : Frequency) :
    (N : ℂ)⁻¹ * (∑ m : ZMod N, UnitAddTorus.mFourier k (rankOneNodeHom N h m)) =
      if (N : ℤ) ∣ dualContact h k then 1 else 0 := by
  classical
  simp only [mFourier_rankOneNode, sum_stdAddChar_mul,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs <;> simp [NeZero.ne (N : ℂ)]

/-- The translation receiver is a literal character multiplier on the genuine torus. -/
theorem rankOneAverage_mFourier (h : ℤ) (k : Frequency) (x : GeometricTwoTorus) :
    rankOneAverage N h (UnitAddTorus.mFourier k) x =
      (if (N : ℤ) ∣ dualContact h k then 1 else 0) * UnitAddTorus.mFourier k x := by
  classical
  unfold rankOneAverage subgroupAverage
  simp_rw [mFourier_translate]
  rw [← Finset.mul_sum]
  calc
    (N : ℂ)⁻¹ * (UnitAddTorus.mFourier k x *
        ∑ m : ZMod N, UnitAddTorus.mFourier k (rankOneNodeHom N h m)) =
      ((N : ℂ)⁻¹ * ∑ m : ZMod N,
        UnitAddTorus.mFourier k (rankOneNodeHom N h m)) * UnitAddTorus.mFourier k x := by ring
    _ = _ := by rw [rankOne_character_average]

/-- Haar translation transports the actual coefficient, with its character phase. -/
theorem mFourierCoeff_translate (f : C(GeometricTwoTorus, ℂ))
    (k : Frequency) (y : GeometricTwoTorus) :
    UnitAddTorus.mFourierCoeff (fun x ↦ f (x + y)) k =
      UnitAddTorus.mFourier k y * UnitAddTorus.mFourierCoeff f k := by
  have hcancel : UnitAddTorus.mFourier k y * UnitAddTorus.mFourier (-k) y = 1 := by
    rw [← UnitAddTorus.mFourier_add]
    simp [UnitAddTorus.mFourier_zero]
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ x : GeometricTwoTorus, UnitAddTorus.mFourier (-k) x * f (x + y)) =
        ∫ x : GeometricTwoTorus, UnitAddTorus.mFourier k y *
          (UnitAddTorus.mFourier (-k) (x + y) * f (x + y)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mFourier_translate]
      calc
        _ = (UnitAddTorus.mFourier k y * UnitAddTorus.mFourier (-k) y) *
            (UnitAddTorus.mFourier (-k) x * f (x + y)) := by rw [hcancel, one_mul]
        _ = _ := by ring
    _ = UnitAddTorus.mFourier k y *
        ∫ x : GeometricTwoTorus, UnitAddTorus.mFourier (-k) (x + y) * f (x + y) :=
      integral_const_mul _ _
    _ = _ := by rw [integral_add_right_eq_self
      (fun x : GeometricTwoTorus ↦ UnitAddTorus.mFourier (-k) x * f x) y]

/-- The character mask acts on the actual Haar Fourier receiver of a continuous field. -/
theorem mFourierCoeff_rankOneAverage (h : ℤ) (f : C(GeometricTwoTorus, ℂ))
    (k : Frequency) :
    UnitAddTorus.mFourierCoeff (rankOneAverage N h f) k =
      (if (N : ℤ) ∣ dualContact h k then 1 else 0) *
        UnitAddTorus.mFourierCoeff f k := by
  classical
  unfold UnitAddTorus.mFourierCoeff rankOneAverage subgroupAverage
  simp only [smul_eq_mul]
  have hrearrange (x : GeometricTwoTorus) :
      UnitAddTorus.mFourier (-k) x *
          ((N : ℂ)⁻¹ * ∑ m : ZMod N, f (x + rankOneNodeHom N h m)) =
        (N : ℂ)⁻¹ * ∑ m : ZMod N,
          UnitAddTorus.mFourier (-k) x * f (x + rankOneNodeHom N h m) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [hrearrange]
  rw [integral_const_mul, integral_finsetSum]
  · change (N : ℂ)⁻¹ * (∑ m : ZMod N,
        UnitAddTorus.mFourierCoeff (fun x ↦ f (x + rankOneNodeHom N h m)) k) = _
    simp_rw [mFourierCoeff_translate]
    rw [← Finset.sum_mul, ← mul_assoc, rankOne_character_average]
    rfl
  · intro m _
    exact continuousMap_integrable_on_compact
      { toFun := fun x : GeometricTwoTorus ↦
          UnitAddTorus.mFourier (-k) x * f (x + rankOneNodeHom N h m)
        continuous_toFun := by fun_prop }

/-- Continuous translation, using the existing continuous-map composition owner. -/
def translateMap (y : GeometricTwoTorus) : C(GeometricTwoTorus, GeometricTwoTorus) where
  toFun x := x + y
  continuous_toFun := by fun_prop

/-- The finite receiver is continuous and linear, so it transports convergent Fourier series. -/
def subgroupAverageCLM (node : ZMod N →+ GeometricTwoTorus) :
    C(GeometricTwoTorus, ℂ) →L[ℂ] C(GeometricTwoTorus, ℂ) :=
  (N : ℂ)⁻¹ • ∑ m : ZMod N, ContinuousMap.compCLM ℂ ℂ (translateMap (node m))

@[simp]
theorem subgroupAverageCLM_apply (node : ZMod N →+ GeometricTwoTorus)
    (f : C(GeometricTwoTorus, ℂ)) (x : GeometricTwoTorus) :
    subgroupAverageCLM node f x = subgroupAverage node f x := by
  simp [subgroupAverageCLM, subgroupAverage, translateMap, smul_eq_mul]

/-- Absolute convergence is paid at the actual Haar receiver before the field is reconstructed. -/
theorem hasSum_rankOneAverage_fourier (h : ℤ) (f : C(GeometricTwoTorus, ℂ))
    (hf : Summable (UnitAddTorus.mFourierCoeff f)) :
    HasSum (fun k : Frequency ↦
      ((if (N : ℤ) ∣ dualContact h k then 1 else 0) *
        UnitAddTorus.mFourierCoeff f k) • UnitAddTorus.mFourier k)
      (subgroupAverageCLM (rankOneNodeHom N h) f) := by
  classical
  have hsum := (subgroupAverageCLM (rankOneNodeHom N h)).hasSum
    (UnitAddTorus.hasSum_mFourier_series_of_summable hf)
  convert hsum using 1
  funext k
  ext x
  simp only [map_smul, subgroupAverageCLM_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change _ = UnitAddTorus.mFourierCoeff f k * rankOneAverage N h (UnitAddTorus.mFourier k) x
  rw [rankOneAverage_mFourier]
  ring

/-- Complete nonzero surviving-mode residual, with no finite-aperture truncation. -/
def dualSpectralResidual (N : ℕ) (h : ℤ) (coeff : Frequency → ℂ) : ℂ :=
  ∑' k : Frequency, if k ≠ 0 ∧ (N : ℤ) ∣ dualContact h k then coeff k else 0

/-- The residual of the subgroup receiver relative to Haar is exactly the full dual alias sum. -/
theorem rankOneAverage_sub_haar_eq_dualSpectralResidual
    (h : ℤ) (f : C(GeometricTwoTorus, ℂ))
    (hf : Summable (UnitAddTorus.mFourierCoeff f)) :
    rankOneAverage N h f 0 - UnitAddTorus.mFourierCoeff f 0 =
      dualSpectralResidual N h (UnitAddTorus.mFourierCoeff f) := by
  classical
  let coeff : Frequency → ℂ := fun k ↦
    (if (N : ℤ) ∣ dualContact h k then 1 else 0) * UnitAddTorus.mFourierCoeff f k
  have hsum : HasSum coeff (rankOneAverage N h f 0) := by
    have heval := (ContinuousMap.evalCLM ℂ (0 : GeometricTwoTorus)).hasSum
      (hasSum_rankOneAverage_fourier (N := N) h f hf)
    simpa only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
      UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply, fourier_eval_zero,
      Finset.prod_const_one, mul_one, subgroupAverageCLM_apply, coeff, rankOneAverage]
      using heval
  have hzero : coeff 0 = UnitAddTorus.mFourierCoeff f 0 := by simp [coeff, dualContact]
  have hsplit := hsum.summable.tsum_eq_add_tsum_ite (0 : Frequency)
  rw [hsum.tsum_eq, hzero] at hsplit
  rw [hsplit, add_sub_cancel_left]
  unfold dualSpectralResidual
  apply tsum_congr
  intro k
  by_cases hk : k = 0 <;> by_cases hd : (N : ℤ) ∣ dualContact h k <;>
    simp [coeff, hk, hd]

/-- The literal normalized pair-kernel reading, including diagonal pairs. -/
def subgroupPairKernelMean (node : ZMod N →+ GeometricTwoTorus)
    (kernel : GeometricTwoTorus → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n : ZMod N, subgroupAverage node kernel (-node n)

theorem subgroupPairKernelMean_eq_average (node : ZMod N →+ GeometricTwoTorus)
    (kernel : GeometricTwoTorus → ℂ) :
    subgroupPairKernelMean node kernel = subgroupAverage node kernel 0 := by
  classical
  have htranslate (n : ZMod N) : subgroupAverage node kernel (-node n) =
      subgroupAverage node kernel 0 := by
    simpa using subgroupAverage_translate node kernel 0 (-n)
  simp only [subgroupPairKernelMean, htranslate, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_mul]

theorem subgroupPairKernelMean_eq_double_sum (node : ZMod N →+ GeometricTwoTorus)
    (kernel : GeometricTwoTorus → ℂ) :
    subgroupPairKernelMean node kernel =
      (N : ℂ)⁻¹ ^ 2 * ∑ n : ZMod N, ∑ m : ZMod N, kernel (node m - node n) := by
  simp only [subgroupPairKernelMean, subgroupAverage, sub_eq_add_neg]
  simp_rw [add_comm (-node _) (node _)]
  rw [← Finset.mul_sum]
  ring

/-- The normalized pair-kernel surplus over its Haar mean retains every nonzero dual mode. -/
theorem rankOne_pairKernel_residual (h : ℤ) (kernel : C(GeometricTwoTorus, ℂ))
    (hkernel : Summable (UnitAddTorus.mFourierCoeff kernel)) :
    subgroupPairKernelMean (rankOneNodeHom N h) kernel -
        UnitAddTorus.mFourierCoeff kernel 0 =
      dualSpectralResidual N h (UnitAddTorus.mFourierCoeff kernel) := by
  rw [subgroupPairKernelMean_eq_average]
  exact rankOneAverage_sub_haar_eq_dualSpectralResidual h kernel hkernel

/-- Nagel's declared one-coordinate Sobolev coefficient, including its constant mode. -/
def nagelWeight (p : ℝ) (k : ℤ) : ℝ :=
  if k = 0 then 1 else p / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)

def nagelTensorWeight (p : ℝ) (k : Frequency) : ℝ :=
  nagelWeight p (k 0) * nagelWeight p (k 1)

@[simp]
theorem nagelTensorWeight_zero (p : ℝ) : nagelTensorWeight p 0 = 1 := by
  simp [nagelTensorWeight, nagelWeight]

/-- Conditional physical-kernel join: the coefficients are those of the actual Haar receiver,
and their convergence is an explicit operand, not an unproved kernel-identification adapter. -/
theorem nagel_pairKernel_residual (h : ℤ) (p : ℝ)
    (kernel : C(GeometricTwoTorus, ℂ))
    (hcoeff : ∀ k : Frequency, UnitAddTorus.mFourierCoeff kernel k =
      (nagelTensorWeight p k : ℂ))
    (hconverges : Summable (UnitAddTorus.mFourierCoeff kernel)) :
    subgroupPairKernelMean (rankOneNodeHom N h) kernel - 1 =
      ∑' k : Frequency, if k ≠ 0 ∧ (N : ℤ) ∣ dualContact h k then
        (nagelTensorWeight p k : ℂ) else 0 := by
  have h := rankOne_pairKernel_residual (N := N) h kernel hconverges
  simpa [dualSpectralResidual, hcoeff] using h

/-! ## Rechart the nodes and their kernel together -/

/-- Transport the addressed subgroup by an additive torus equivalence. -/
def transportedNode (A : GeometricTwoTorus ≃+ GeometricTwoTorus)
    (node : ZMod N →+ GeometricTwoTorus) : ZMod N →+ GeometricTwoTorus :=
  A.toAddMonoidHom.comp node

/-- The kernel in the new frame is `c_A(t) = c(A⁻¹ t)`. -/
def transportedKernel (A : GeometricTwoTorus ≃+ GeometricTwoTorus)
    (kernel : GeometricTwoTorus → ℂ) : GeometricTwoTorus → ℂ :=
  fun t ↦ kernel (A.symm t)

theorem subgroupAverage_transport (A : GeometricTwoTorus ≃+ GeometricTwoTorus)
    (node : ZMod N →+ GeometricTwoTorus) (f : GeometricTwoTorus → ℂ)
    (x : GeometricTwoTorus) :
    subgroupAverage (transportedNode A node) (transportedKernel A f) (A x) =
      subgroupAverage node f x := by
  simp [subgroupAverage, transportedNode, transportedKernel, ← map_add]

/-- Recharting preserves the literal pair-kernel objective only with the transported kernel. -/
theorem subgroupPairKernelMean_transport (A : GeometricTwoTorus ≃+ GeometricTwoTorus)
    (node : ZMod N →+ GeometricTwoTorus) (kernel : GeometricTwoTorus → ℂ) :
    subgroupPairKernelMean (transportedNode A node) (transportedKernel A kernel) =
      subgroupPairKernelMean node kernel := by
  rw [subgroupPairKernelMean_eq_average, subgroupPairKernelMean_eq_average]
  simpa using subgroupAverage_transport A node kernel 0

/-- The recharted literal pair reading retains the complete residual of its originating Haar
receiver. This uses the transported kernel, without assuming an unchanged anisotropic kernel. -/
theorem transported_pairKernel_residual (A : GeometricTwoTorus ≃+ GeometricTwoTorus)
    (h : ℤ) (kernel : C(GeometricTwoTorus, ℂ))
    (hkernel : Summable (UnitAddTorus.mFourierCoeff kernel)) :
    subgroupPairKernelMean (transportedNode A (rankOneNodeHom N h))
        (transportedKernel A kernel) - UnitAddTorus.mFourierCoeff kernel 0 =
      dualSpectralResidual N h (UnitAddTorus.mFourierCoeff kernel) := by
  rw [subgroupPairKernelMean_transport]
  exact rankOne_pairKernel_residual h kernel hkernel

/-- An integer matrix acts directly on the existing quotient torus. -/
def integerTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ) :
    GeometricTwoTorus →+ GeometricTwoTorus where
  toFun x i := A i 0 • x 0 + A i 1 • x 1
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp only [Pi.add_apply, zsmul_add]; abel

theorem integerTorusMap_one :
    integerTorusMap (1 : Matrix (Fin 2) (Fin 2) ℤ) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i <;> simp [integerTorusMap]

theorem integerTorusMap_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    integerTorusMap (A * B) = (integerTorusMap A).comp (integerTorusMap B) := by
  apply AddMonoidHom.ext
  intro x
  funext i
  change (A * B) i 0 • x 0 + (A * B) i 1 • x 1 =
    A i 0 • (B 0 0 • x 0 + B 0 1 • x 1) +
      A i 1 • (B 1 0 • x 0 + B 1 1 • x 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, add_zsmul, mul_zsmul, zsmul_add]
  abel

/-- A determinant-one integral matrix gives an actual invertible quotient-torus transport. -/
def slTorusEquiv (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    GeometricTwoTorus ≃+ GeometricTwoTorus where
  toFun := integerTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ)
  invFun := integerTorusMap
    ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  left_inv x := by
    have hleft : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) *
        (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
        using congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) ℤ ↦
          (B : Matrix (Fin 2) (Fin 2) ℤ)) (inv_mul_cancel A)
    change ((integerTorusMap
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)).comp
      (integerTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ))) x = x
    rw [← integerTorusMap_mul, hleft, integerTorusMap_one]
    rfl
  right_inv x := by
    have hright : (A : Matrix (Fin 2) (Fin 2) ℤ) *
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
        using congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) ℤ ↦
          (B : Matrix (Fin 2) (Fin 2) ℤ)) (mul_inv_cancel A)
    change ((integerTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ)).comp
      (integerTorusMap
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ))) x = x
    rw [← integerTorusMap_mul, hright, integerTorusMap_one]
    rfl
  map_add' := (integerTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ)).map_add

theorem fourier_phase_add (k : ℤ) (x y : UnitAddCircle) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Pulling back a character uses the transpose matrix on its integer frequency. -/
theorem mFourier_integerTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ)
    (k : Frequency) (x : GeometricTwoTorus) :
    UnitAddTorus.mFourier k (integerTorusMap A x) =
      UnitAddTorus.mFourier (Matrix.mulVec A.transpose k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two]
  change fourier (k 0) (A 0 0 • x 0 + A 0 1 • x 1) *
    fourier (k 1) (A 1 0 • x 0 + A 1 1 • x 1) =
      fourier ((Matrix.mulVec A.transpose k) 0) (x 0) *
        fourier ((Matrix.mulVec A.transpose k) 1) (x 1)
  simp only [fourier_phase_add, fourier_zsmul,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, fourier_add]
  simp only [mul_comm (k 0), mul_comm (k 1)]
  ring

/-- Frequencies carried to the new frame move by `A⁻ᵀ`, including every dual alias. -/
def transportedFrequency (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (k : Frequency) : Frequency :=
  Matrix.mulVec
    (((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).transpose) k

theorem mFourier_transportedFrequency (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (k : Frequency) (x : GeometricTwoTorus) :
    UnitAddTorus.mFourier (transportedFrequency A k) (slTorusEquiv A x) =
      UnitAddTorus.mFourier k x := by
  rw [transportedFrequency, ← mFourier_integerTorusMap]
  change UnitAddTorus.mFourier k ((slTorusEquiv A).symm (slTorusEquiv A x)) = _
  rw [AddEquiv.symm_apply_apply]

/-- The transported frequency and transported lattice retain precisely the same character mask. -/
theorem transported_character_average (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : ℤ) (k : Frequency) :
    (N : ℂ)⁻¹ * (∑ m : ZMod N, UnitAddTorus.mFourier (transportedFrequency A k)
      (transportedNode (slTorusEquiv A) (rankOneNodeHom N h) m)) =
      if (N : ℤ) ∣ dualContact h k then 1 else 0 := by
  change (N : ℂ)⁻¹ * (∑ m : ZMod N, UnitAddTorus.mFourier (transportedFrequency A k)
    (slTorusEquiv A (rankOneNodeHom N h m))) = _
  simp_rw [mFourier_transportedFrequency]
  exact rankOne_character_average h k

/-! ## Fibonacci specialization, without an optimality claim -/

/-- The displayed complex exponential is the existing torus character, not a second phase model. -/
theorem mFourier_rankOneNode_exp (h : ℤ) (k : Frequency) (m : ZMod N) :
    UnitAddTorus.mFourier k (rankOneNodeHom N h m) =
      Complex.exp (2 * Real.pi * Complex.I * (dualContact h k : ℂ) *
        (m.val : ℂ) / (N : ℂ)) := by
  rw [mFourier_rankOneNode]
  have hcast : ((dualContact h k * (m.val : ℤ) : ℤ) : ZMod N) =
      (dualContact h k : ZMod N) * m := by simp
  rw [← hcast, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

theorem rankOne_exponential_average (h : ℤ) (k : Frequency) :
    (N : ℂ)⁻¹ * (∑ m : ZMod N,
      Complex.exp (2 * Real.pi * Complex.I * (dualContact h k : ℂ) *
        (m.val : ℂ) / (N : ℂ))) =
      if (N : ℤ) ∣ dualContact h k then 1 else 0 := by
  simp_rw [← mFourier_rankOneNode_exp]
  exact rankOne_character_average h k

/-- At `N=F_l`, `h=F_(l-1)`, the exact mask is the Fibonacci contact congruence. -/
theorem fibonacci_exponential_average (l : ℕ) [NeZero (Nat.fib l)] (k : Frequency) :
    (Nat.fib l : ℂ)⁻¹ * (∑ m : ZMod (Nat.fib l),
      Complex.exp (2 * Real.pi * Complex.I *
        ((k 0 + (Nat.fib (l - 1) : ℤ) * k 1 : ℤ) : ℂ) *
        (m.val : ℂ) / (Nat.fib l : ℂ))) =
      if (Nat.fib l : ℤ) ∣ k 0 + (Nat.fib (l - 1) : ℤ) * k 1 then 1 else 0 :=
  rankOne_exponential_average (N := Nat.fib l) (Nat.fib (l - 1)) k

/-- The same rational slope keeps the existing carry-word lock law at every source phase. -/
theorem fibonacci_carry_word (l : ℕ) [NeZero (Nat.fib l)] (ρ : ℝ) (m : ℤ) :
    (∑ i ∈ Finset.range (Nat.fib l), Holonics.Aeon.Clock.CarryWord.carry
      ((Nat.fib (l - 1) : ℝ) / Nat.fib l) ρ (m + i)) = (Nat.fib (l - 1) : ℤ) :=
  Holonics.Aeon.Clock.CarryWord.sum_carry_period_of_rational
    (p := (Nat.fib (l - 1) : ℤ)) (NeZero.pos (Nat.fib l)) (by push_cast; rfl) m

section Audit

#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOneNodeHom_apply
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOneNodeHom_intCast
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOneNodeHom_injective
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.card_rankOneSubgroup
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupAverage_translate
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupAverage_idempotent
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOneAverage_idempotent
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourier_translate
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.fourier_zsmul
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.fourier_toAddCircle
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourier_rankOneNode
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.sum_stdAddChar_mul
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOne_character_average
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOneAverage_mFourier
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourierCoeff_translate
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourierCoeff_rankOneAverage
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupAverageCLM_apply
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.hasSum_rankOneAverage_fourier
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOneAverage_sub_haar_eq_dualSpectralResidual
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupPairKernelMean_eq_average
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupPairKernelMean_eq_double_sum
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOne_pairKernel_residual
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.nagelTensorWeight_zero
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.nagel_pairKernel_residual
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupAverage_transport
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.subgroupPairKernelMean_transport
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.transported_pairKernel_residual
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.integerTorusMap_one
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.integerTorusMap_mul
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.fourier_phase_add
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourier_integerTorusMap
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourier_transportedFrequency
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.transported_character_average
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.mFourier_rankOneNode_exp
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.rankOne_exponential_average
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.fibonacci_exponential_average
#print axioms Holonics.Geometry.FiniteTorusSubgroupReceiver.fibonacci_carry_word

end Audit

end Holonics.Geometry.FiniteTorusSubgroupReceiver
