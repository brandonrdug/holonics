import Holonics.Physics.Fluid.Singularity
import Holonics.Holarchy.Globe
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# Fluid.Body: a closed body in a stream is a globe, and a net emission opens it into a tube

[definition] The egg record §4 for rebuild step 6, K3 (#74). A uniform stream `U` along `x` with
point singularities of strengths `c_k = m_k + iΓ_k` at `z_k` (`Γ_k` the clockwise circulation,
`Singularity.circulation_flux_jump`) has the lifted potential

```text
F = U z + Σ_k (c_k / 2π) ℓ_k,        ℓ_k ∈ logFibre (z − z_k : 1)
```

(`liftedPotential`), each logarithm carried as a lift of its undivided ratio
(`Objects/Ratio.logFibre`). A **dividing streamline** keeps the stream function `ψ = Im F`
constant along it, read through the lifts continued along the curve. Along a loop `γ` avoiding the
sites, each ratio `(γ(t) − z_k : 1)` is a path in `ℂ ∖ {0}` and its lift is the path lifting
through the covering `exp` (`siteLift`, Mathlib `IsCoveringMap.liftPath` over
`Complex.isCoveringMap_exp`); it returns advanced by `2πi n_k`, `n_k` the loop's winding around
`z_k` (`winding`, `siteLift_advance`).

[proved-derived; formal-checked]

* **The loop jump.** Over a loop the potential jumps by `i Σ c_k n_k` with whole windings `n_k`
  (`loop_jump`, from `Singularity.potential_jump`), so the stream function jumps by the enclosed
  emission `Σ m_k n_k` (`stream_jump`).
* **Necessity (Gauss/Rankine).** A closed loop avoiding the sites along which `ψ` is constant
  (a closed dividing streamline, read through the continued lifts) balances its windings,
  `Σ m_k n_k = 0` (`closed_streamline_balances`); if it winds once around every singularity, the
  net strength is zero, `Σ m_k = 0` (`closed_streamline_net_zero`). The winding counts turns: the
  counterclockwise circle about a site winds once (`circleLoop_winding`).
* **The same law on a Holarchy block.** A block whose membrane is a streamline (no current on any
  of its faces) encloses zero net divergence (`streamline_membrane_net_zero`, composing
  `Holarchy/Globe.blockMembrane_gauss`); the block's membrane bounds its interior by construction
  (`Holarchy/Globe.constituentMembrane_boundsInterior`), which is clause (3) of relative
  completeness (`Objects/RelativeCompleteness`).

[counterexample; formal-checked]

* **Nonzero net emission opens the body into a tube** (Rankine's half-body: one source `m > 0` in a
  stream `U > 0`). Its dividing streamline `ψ = m/2` reaches every station `x₀ > 0` downstream at
  a height strictly inside `(0, m/(2U))` (`halfBody_reaches`), every point of its upper branch lies
  below the half-width `m/(2U)` (`halfBody_width`), and it is unbounded (`halfBody_unbounded`):
  no closed curve, a tube of asymptotic width `m/U` carrying the emitted flux `U · m/U = m`.
* **A tube's lateral streamlines enclose emission that leaves through its ends**: on the square of
  `Objects/RelativeCompleteness`, a current with no flux through the lateral membrane encloses
  divergence `2`, and that membrane bounds nothing (`tube_encloses_emission`, composing
  `tubeMembrane_escapes`).

[open] **Sufficiency** (zero net strength gives a closed dividing streamline, the Rankine oval) is
not formalized. The join to relative completeness is clause (3) only: a flux-only exterior receiver
reads a closed body's monopole as zero, so clause (1) would need a receiver of its dipole moment
(the doublet), and clause (2) an interior motion; neither is stated here (#62).
-/

noncomputable section

namespace Holonics.Physics.Fluid.Body

open Complex Matrix
open Holonics.Objects.Ratio Holonics.Geometry
open Holonics.Physics.Fluid.Singularity

/-! ## 1. The lifted potential and its loop jump -/

section Lifted

variable {ι : Type*} [Fintype ι]

/-- [definition] **The lifted potential** of a uniform stream `U` and point singularities of
strengths `c`, read with the lifts `ℓ`. -/
def liftedPotential (U : ℝ) (c : ι → ℂ) (z : ℂ) (ℓ : ι → ℂ) : ℂ :=
  U * z + ∑ k, c k / (2 * Real.pi) * ℓ k

/-- [proved-derived; formal-checked] **The loop jump**: two lifts of the same point's ratios differ
by whole windings, and the potential by `i Σ c_k n_k`. -/
theorem loop_jump (U : ℝ) (c : ι → ℂ) (z₀ : ℂ) (sites : ι → ℂ) {ℓ ℓ' : ι → ℂ}
    (hℓ : ∀ k, ℓ k ∈ logFibre (holonRatio (z₀ - sites k) 1))
    (hℓ' : ∀ k, ℓ' k ∈ logFibre (holonRatio (z₀ - sites k) 1)) :
    ∃ n : ι → ℤ, liftedPotential U c z₀ ℓ' - liftedPotential U c z₀ ℓ = I * ∑ k, c k * n k := by
  have h : ∀ k, ∃ n : ℤ, c k / (2 * Real.pi) * ℓ' k - c k / (2 * Real.pi) * ℓ k = I * c k * n :=
    fun k => potential_jump (c k) one_ne_zero (hℓ k) (hℓ' k)
  choose n hn using h
  refine ⟨n, ?_⟩
  simp only [liftedPotential, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, hn,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- [proved-derived; formal-checked] **The stream function jumps by the enclosed emission**
`Σ m_k n_k`. -/
theorem stream_jump (c : ι → ℂ) (n : ι → ℤ) :
    (I * ∑ k, c k * n k).im = ∑ k, (c k).re * n k := by
  simp [Complex.im_sum]

end Lifted

/-! ## 2. A closed dividing streamline: path lifting around the sites -/

section Loop

variable {ι : Type*} [Fintype ι]

/-- [definition] **The ratio `(γ(t) − s : 1)` along a loop avoiding the site `s`**, as a path in
`ℂ ∖ {0}`, the base of the covering `exp`. -/
def sitePath (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s) :
    C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun t => ⟨γ t - s, sub_ne_zero.mpr (havoid t)⟩,
    (γ.continuous.sub continuous_const).subtype_mk _⟩

theorem sitePath_zero (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s) :
    sitePath γ s havoid 0 =
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
        (Complex.log (γ 0 - s)) :=
  Subtype.ext (by simp [sitePath, Complex.exp_log (sub_ne_zero.mpr (havoid 0))])

/-- [definition] **The lift continued along the loop**: the path lifting of `sitePath` through the
covering `exp : ℂ → ℂ ∖ {0}` (`Complex.isCoveringMap_exp`, `IsCoveringMap.liftPath`), starting at the
principal logarithm. -/
def siteLift (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s) : C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (sitePath γ s havoid) (Complex.log (γ 0 - s))
    (sitePath_zero γ s havoid)

theorem exp_siteLift (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s) (t : unitInterval) :
    Complex.exp (siteLift γ s havoid t) = γ t - s := by
  have h := congrArg Subtype.val (congrFun
    (Complex.isCoveringMap_exp.liftPath_lifts (sitePath γ s havoid) _ (sitePath_zero γ s havoid)) t)
  simpa [sitePath, siteLift] using h

/-- [proved-derived; formal-checked] **Every point of the continued lift is a lift of the ratio**
`(γ(t) − s : 1)` (`Objects/Ratio.logFibre`). -/
theorem siteLift_mem (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s) (t : unitInterval) :
    siteLift γ s havoid t ∈ logFibre (holonRatio (γ t - s) 1) := by
  change Complex.exp (siteLift γ s havoid t) * 1 = γ t - s
  rw [mul_one, exp_siteLift]

theorem siteLift_advance_exists (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s)
    (hloop : γ 0 = γ 1) :
    ∃ n : ℤ, siteLift γ s havoid 1 = siteLift γ s havoid 0 + n * (2 * Real.pi * I) := by
  have h1 := siteLift_mem γ s havoid 1
  rw [← hloop] at h1
  exact (logFibre_torsor (r := holonRatio (γ 0 - s) 1) one_ne_zero
    (siteLift_mem γ s havoid 0)).mp h1

/-- [definition] **The winding of a loop around a site**: the whole turns by which the continued
lift advances once around the loop. -/
def winding (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s) (hloop : γ 0 = γ 1) : ℤ :=
  (siteLift_advance_exists γ s havoid hloop).choose

/-- [proved-derived; formal-checked] **Path lifting advances each lift by its winding**:
`ℓ(1) = ℓ(0) + 2πi n`. -/
theorem siteLift_advance (γ : C(unitInterval, ℂ)) (s : ℂ) (havoid : ∀ t, γ t ≠ s)
    (hloop : γ 0 = γ 1) :
    siteLift γ s havoid 1 =
      siteLift γ s havoid 0 + winding γ s havoid hloop * (2 * Real.pi * I) :=
  (siteLift_advance_exists γ s havoid hloop).choose_spec

/-- [proved-derived; formal-checked] **Necessity (Gauss/Rankine): a closed dividing streamline
balances its windings.** Let `γ` be a loop avoiding every site, and read the potential along it
through the lifts continued along `γ` (`siteLift`). If the stream function `ψ = Im F` is constant
along `γ`, then `Σ m_k n_k = 0`, with `n_k` the winding of `γ` around `z_k`. -/
theorem closed_streamline_balances (U : ℝ) (c : ι → ℂ) (sites : ι → ℂ) (γ : C(unitInterval, ℂ))
    (hloop : γ 0 = γ 1) (havoid : ∀ t k, γ t ≠ sites k)
    (hstream : ∀ t, (liftedPotential U c (γ t) fun k => siteLift γ (sites k) (havoid · k) t).im =
      (liftedPotential U c (γ 0) fun k => siteLift γ (sites k) (havoid · k) 0).im) :
    ∑ k, (c k).re * winding γ (sites k) (havoid · k) hloop = 0 := by
  have hjump : (liftedPotential U c (γ 1) fun k => siteLift γ (sites k) (havoid · k) 1) -
      (liftedPotential U c (γ 0) fun k => siteLift γ (sites k) (havoid · k) 0) =
      I * ∑ k, c k * winding γ (sites k) (havoid · k) hloop := by
    simp only [liftedPotential, ← hloop, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [siteLift_advance γ (sites k) (havoid · k) hloop]
    have := two_pi_ne_zero
    field_simp
    ring
  have := congrArg Complex.im hjump
  rw [Complex.sub_im, hstream 1, sub_self, stream_jump] at this
  exact this.symm

/-- [proved-derived; formal-checked] **Necessity (Gauss/Rankine): a closed body has zero net
strength.** A closed dividing streamline that winds once around every singularity forces
`Σ m_k = 0`. -/
theorem closed_streamline_net_zero (U : ℝ) (c : ι → ℂ) (sites : ι → ℂ) (γ : C(unitInterval, ℂ))
    (hloop : γ 0 = γ 1) (havoid : ∀ t k, γ t ≠ sites k)
    (honce : ∀ k, winding γ (sites k) (havoid · k) hloop = 1)
    (hstream : ∀ t, (liftedPotential U c (γ t) fun k => siteLift γ (sites k) (havoid · k) t).im =
      (liftedPotential U c (γ 0) fun k => siteLift γ (sites k) (havoid · k) 0).im) :
    ∑ k, (c k).re = 0 := by
  have := closed_streamline_balances U c sites γ hloop havoid hstream
  simpa [honce] using this

/-- [definition] The counterclockwise circle of radius `r` about `s`. -/
def circleLoop (s : ℂ) (r : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => s + r * Complex.exp (2 * Real.pi * I * ((t : ℝ) : ℂ)), by fun_prop⟩

theorem circleLoop_closed (s : ℂ) (r : ℝ) : circleLoop s r 0 = circleLoop s r 1 := by
  simp only [circleLoop, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one,
    Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one, Complex.exp_zero,
    Complex.exp_two_pi_mul_I]

theorem circleLoop_avoids (s : ℂ) {r : ℝ} (hr : 0 < r) (t : unitInterval) :
    circleLoop s r t ≠ s := by
  simp only [circleLoop, ContinuousMap.coe_mk, ne_eq, add_eq_left, mul_eq_zero,
    Complex.ofReal_eq_zero, Complex.exp_ne_zero, or_false]
  exact hr.ne'

/-- [proved-derived; formal-checked] **The winding counts turns**: the counterclockwise circle
about a site winds once around it, so `closed_streamline_net_zero`'s hypothesis is the winding a
simple closed body has. -/
theorem circleLoop_winding (s : ℂ) {r : ℝ} (hr : 0 < r) :
    winding (circleLoop s r) s (circleLoop_avoids s hr) (circleLoop_closed s r) = 1 := by
  set Λ : C(unitInterval, ℂ) :=
    ⟨fun t => (Real.log r : ℂ) + 2 * Real.pi * I * ((t : ℝ) : ℂ), by fun_prop⟩ with hΛ
  have hlift : Λ = siteLift (circleLoop s r) s (circleLoop_avoids s hr) := by
    refine (Complex.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨funext fun t => ?_, ?_⟩
    · refine Subtype.ext ?_
      simp only [Function.comp_apply, hΛ, ContinuousMap.coe_mk, sitePath, circleLoop,
        add_sub_cancel_left, Complex.exp_add]
      rw [← Complex.ofReal_exp, Real.exp_log hr]
    · simp only [hΛ, ContinuousMap.coe_mk, circleLoop, Set.Icc.coe_zero, Complex.ofReal_zero,
        mul_zero, Complex.exp_zero, mul_one, add_sub_cancel_left, add_zero]
      exact Complex.ofReal_log hr.le
  have hadv := siteLift_advance (circleLoop s r) s (circleLoop_avoids s hr) (circleLoop_closed s r)
  rw [← hlift] at hadv
  simp only [hΛ, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one, Complex.ofReal_zero,
    Complex.ofReal_one, mul_zero, mul_one, add_zero, add_right_inj] at hadv
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn : ((winding (circleLoop s r) s (circleLoop_avoids s hr) (circleLoop_closed s r) : ℤ) : ℂ)
      = ((1 : ℤ) : ℂ) := by
    have := mul_right_cancel₀ h2pi (hadv.symm.trans (one_mul _).symm)
    simpa using this
  exact_mod_cast hn

end Loop


/-! ## 3. The half-body: nonzero net emission opens a tube -/

/-- [definition] The stream function of a source `m` at the origin in a uniform stream `U`, in
the principal chart of the angle. -/
def halfBodyStream (U m : ℝ) (z : ℂ) : ℝ := U * z.im + m / (2 * Real.pi) * Complex.arg z

theorem arg_pos_of_im_pos {z : ℂ} (h : 0 < z.im) : 0 < Complex.arg z := by
  have h0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr h.le
  rcases h0.lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (Complex.arg_eq_zero_iff.mp h1.symm).2 h.ne'

/-- [counterexample; formal-checked] **The half-body reaches every downstream station**: for
`U, m > 0` and every `x₀ > 0` the dividing streamline `ψ = m/2` passes through `x₀ + iy` with
`0 < y < m/(2U)`. -/
theorem halfBody_reaches {U m : ℝ} (hU : 0 < U) (hm : 0 < m) {x₀ : ℝ} (hx : 0 < x₀) :
    ∃ y, 0 < y ∧ y < m / (2 * U) ∧ halfBodyStream U m ((x₀ : ℂ) + y * I) = m / 2 := by
  set top := m / (2 * U)
  have htop : 0 < top := by positivity
  set g : ℝ → ℝ := fun y => halfBodyStream U m ((x₀ : ℂ) + y * I)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcont : ContinuousOn g (Set.Icc 0 top) := by
    refine Continuous.continuousOn ?_
    have hpath : Continuous fun y : ℝ => (x₀ : ℂ) + y * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have harg : Continuous fun y : ℝ => Complex.arg ((x₀ : ℂ) + y * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      refine (Complex.continuousAt_arg ?_).comp hpath.continuousAt
      rw [Complex.mem_slitPlane_iff]
      left; simp [hx]
    have him : Continuous fun y : ℝ => ((x₀ : ℂ) + y * I).im :=
      Complex.continuous_im.comp hpath
    exact (continuous_const.mul him).add (continuous_const.mul harg)
  have hg0 : g 0 = 0 := by
    simp only [g, halfBodyStream]
    simp [Complex.arg_ofReal_of_nonneg hx.le]
  have hgtop : m / 2 < g top := by
    simp only [g, halfBodyStream]
    have him : ((x₀ : ℂ) + top * I).im = top := by simp
    have harg : 0 < Complex.arg ((x₀ : ℂ) + top * I) := arg_pos_of_im_pos (by rw [him]; exact htop)
    rw [him]
    have hUtop : U * top = m / 2 := by simp only [top]; field_simp
    rw [hUtop]
    have : 0 < m / (2 * Real.pi) * Complex.arg ((x₀ : ℂ) + top * I) := by positivity
    linarith
  obtain ⟨y, ⟨hy0, hytop⟩, hy⟩ :=
    intermediate_value_Icc htop.le hcont ⟨by rw [hg0]; positivity, hgtop.le⟩
  refine ⟨y, ?_, ?_, hy⟩
  · rcases hy0.lt_or_eq with h | h
    · exact h
    · rw [← h, hg0] at hy; linarith
  · rcases hytop.lt_or_eq with h | h
    · exact h
    · rw [h] at hy; linarith

/-- [counterexample; formal-checked] **The half-body is below its asymptotic half-width**: every
point of the upper branch of `ψ = m/2` has `0 < y < m/(2U)`. -/
theorem halfBody_width {U m : ℝ} (hU : 0 < U) (hm : 0 < m) {z : ℂ} (hz : 0 < z.im)
    (hψ : halfBodyStream U m z = m / 2) : z.im < m / (2 * U) := by
  have harg := arg_pos_of_im_pos hz
  have hpos : 0 < m / (2 * Real.pi) * Complex.arg z := by
    have := Real.pi_pos; positivity
  unfold halfBodyStream at hψ
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- [counterexample; formal-checked] **The half-body is unbounded**: its dividing streamline
reaches beyond every radius, so it is no closed curve. -/
theorem halfBody_unbounded {U m : ℝ} (hU : 0 < U) (hm : 0 < m) (R : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ halfBodyStream U m z = m / 2 ∧ R < ‖z‖ := by
  obtain ⟨y, hy0, -, hy⟩ := halfBody_reaches hU hm (x₀ := max R 0 + 1) (by positivity)
  refine ⟨(↑(max R 0 + 1) : ℂ) + y * I, by simpa using hy0, hy, ?_⟩
  have hre : ((↑(max R 0 + 1) : ℂ) + y * I).re = max R 0 + 1 := by simp
  calc R < max R 0 + 1 := by linarith [le_max_left R 0]
    _ = |((↑(max R 0 + 1) : ℂ) + y * I).re| := by rw [hre, abs_of_pos (by positivity)]
    _ ≤ ‖(↑(max R 0 + 1) : ℂ) + y * I‖ := Complex.abs_re_le_norm _

/-! ## 4. The same law on a Holarchy block -/

section Block

open HolarchyCore Holonics.Objects.RelativeCompleteness

variable {𝕜 : Type*} [Field 𝕜] {Block : Type*}

/-- [proved-derived; formal-checked] **A streamline membrane encloses zero net divergence**: when
the current vanishes on every face of a block's membrane, the divergence summed over the block is
zero (`Holarchy/Globe.blockMembrane_gauss`). -/
theorem streamline_membrane_net_zero (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜)
    (g : Grain K.C₂ Block) (b : Block) (j : K.C₁ → 𝕜)
    (hstream : ∀ f, (blockMembrane K orient g b).surface f ≠ 0 → j f = 0) :
    (K.d₂ᵀ *ᵥ j) ⬝ᵥ (blockMembrane K orient g b).interiorChain = 0 := by
  rw [← (blockMembrane_gauss K orient g b j 0).1]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases h : (blockMembrane K orient g b).surface f = 0
  · rw [h, mul_zero]
  · rw [hstream f h, zero_mul]

/-- [proved-derived; formal-checked] The block's membrane bounds its interior: clause (3) of
relative completeness holds for every block (`constituentMembrane_boundsInterior`). -/
theorem block_bounds (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (b : Block) :
    (blockMembrane K orient g b).BoundsInterior :=
  constituentMembrane_boundsInterior _ _ _ _

end Block

/-- [counterexample; formal-checked] **A tube's lateral streamlines enclose emission that leaves
through its ends**: on the square, the current `(0, 1, 0, −1)` has no flux through the lateral
membrane `e₀ − e₂`, encloses divergence `2`, and the lateral membrane bounds nothing
(`Objects/RelativeCompleteness.tubeMembrane_escapes`). -/
theorem tube_encloses_emission :
    (![0, 1, 0, -1] : Fin 4 → ℚ) ⬝ᵥ Holonics.Objects.RelativeCompleteness.tubeMembrane.surface = 0 ∧
      (![0, 1, 0, -1] : Fin 4 → ℚ) ⬝ᵥ Holonics.Objects.RelativeCompleteness.squareBoundary₂ 1 = 2 ∧
      ¬ Holonics.Objects.RelativeCompleteness.tubeMembrane.Bounds := by
  refine ⟨?_, ?_, Holonics.Objects.RelativeCompleteness.tubeMembrane_escapes.2⟩
  · simp [Holonics.Objects.RelativeCompleteness.tubeMembrane, dotProduct, Fin.sum_univ_four]
  · simp [Holonics.Objects.RelativeCompleteness.squareBoundary₂, dotProduct, Fin.sum_univ_four]
    norm_num

section Audit

#print axioms loop_jump
#print axioms siteLift_advance
#print axioms closed_streamline_balances
#print axioms closed_streamline_net_zero
#print axioms circleLoop_winding
#print axioms halfBody_reaches
#print axioms halfBody_unbounded
#print axioms streamline_membrane_net_zero
#print axioms tube_encloses_emission

end Audit

end Holonics.Physics.Fluid.Body
