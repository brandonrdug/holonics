import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.LocallyFinsupp
import ElementaryHolonics.Millennium.Separation

/-!
# RH/Xi: the entire completed zeta and the fixed locus of its reflection

The object the Riemann hypothesis is about is not a function but a **function together
with an involution it is invariant under**.  Mathlib supplies the first half: `Λ₀` is
entire and `Λ₀(1−s) = Λ₀(s)`.  This file adds the second, which is this repository's
own law — *placement is the fixed locus of the involution the object carries*:

* the **linear** reflection `s ↦ 1 − s` fixes exactly the single point `1/2`;
* the **anti-linear** composite `J s = 1 − s̄` fixes exactly the line `Re s = 1/2`.

So the critical line is not a coordinate someone chose; it is the fixed locus of the
anti-linear involution the functional equation and conjugation generate together.

**Nothing here claims anything about where the zeros are.**  Every `theorem` is
discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.RH

open Complex

/-- **THE ENTIRE COMPLETED ZETA STANDS, WITH ITS REFLECTION.**  Mathlib's `Λ₀` is entire
and satisfies `Λ₀(1−s) = Λ₀(s)`: the object RH is about is a function together with an
involution it is invariant under. -/
theorem theEntireXiExists :
    Differentiable ℂ completedRiemannZeta₀ ∧
      ∀ s : ℂ, completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  ⟨differentiable_completedZeta₀, completedRiemannZeta₀_one_sub⟩

/-- **THE CRITICAL LINE IS THE FIXED LOCUS OF THE REFLECTION.**  The functional
equation's involution `s ↦ 1 − s` is linear and fixes only the point `1/2`; composing it
with conjugation gives the **anti-linear** involution `J s = 1 − s̄`, whose fixed locus is
exactly the line `Re s = 1/2`.  Placement is the fixed locus of the involution the
object carries — stated here, proved, with no claim whatever about where the zeros are. -/
theorem theCriticalLineIsTheFixedLocus (s : ℂ) :
    1 - (starRingEnd ℂ) s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re]; linarith
    · simp [Complex.sub_im, Complex.conj_im]

/-- The linear half of the reflection fixes a single point, not a line — which is why
the anti-linear composite is the one that carries RH's geometry. -/
theorem theLinearReflectionFixesOnlyOnePoint (s : ℂ) : 1 - s = s ↔ s = 1 / 2 := by
  constructor
  · intro h; linear_combination (-(1:ℂ)/2) * h
  · intro h; rw [h]; norm_num

/-- **THE ZERO SET IS REFLECTION-STABLE**, and a zero off the fixed locus is never
alone: the reflection carries it to a *different* zero.  On the fixed locus a zero can
be its own reflection.  So the critical line is exactly where the reflection stops
separating a zero from itself. -/
theorem theZeroSetIsReflectionStable {s : ℂ} (h : completedRiemannZeta₀ s = 0) :
    completedRiemannZeta₀ (1 - s) = 0 ∧ (1 - s = s ↔ s = 1 / 2) := by
  refine ⟨?_, theLinearReflectionFixesOnlyOnePoint s⟩
  rw [completedRiemannZeta₀_one_sub, h]

/-- The orbit count: off the fixed point a zero has a distinct partner; at it, it is its
own. -/
theorem theOffLineZeroIsNeverAlone {s : ℂ} (h : completedRiemannZeta₀ s = 0)
    (hne : s ≠ 1 / 2) :
    completedRiemannZeta₀ (1 - s) = 0 ∧ 1 - s ≠ s :=
  ⟨(theZeroSetIsReflectionStable h).1,
   fun hc => hne ((theLinearReflectionFixesOnlyOnePoint s).mp hc)⟩

/-- **THE FIXED LOCUS FORCES THE VALUE REAL.**  A function carrying the reflection-and-
conjugation symmetry `f(1 − s̄) = conj(f s)` must take **real** values exactly on the
fixed locus of that anti-linear involution — the critical line.  This is the
self-conjugate seam: placement is where a value is forced to equal its own conjugate. -/
theorem theFixedLocusForcesTheValueReal {f : ℂ → ℂ}
    (hsym : ∀ s, f (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (f s))
    {s : ℂ} (hs : s.re = 1 / 2) : (f s).im = 0 := by
  have hfix : 1 - (starRingEnd ℂ) s = s := (theCriticalLineIsTheFixedLocus s).mpr hs
  have h := hsym s
  rw [hfix] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- And the converse direction of the seam: off the fixed locus the symmetry relates
**two different points**, so it constrains a pair rather than a value. -/
theorem theSymmetryOffTheLocusRelatesTwoPoints {f : ℂ → ℂ}
    (hsym : ∀ s, f (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (f s))
    {s : ℂ} (hs : s.re ≠ 1 / 2) :
    1 - (starRingEnd ℂ) s ≠ s ∧
      f (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (f s) :=
  ⟨fun hc => hs ((theCriticalLineIsTheFixedLocus s).mp hc), hsym s⟩

/-! ## The prime side of Weil's pairing -/

section Weil
open ArithmeticFunction

/-- **THE FINITE-PLACE TERM IS THE LOGARITHMIC DERIVATIVE.**  The prime side of the
explicit formula is the von Mangoldt series, and on the half-plane it is exactly
`−ζ′/ζ`.  This half of Weil's pairing is fully available. -/
theorem theFinitePlaceTermIsTheLogarithmicDerivative {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s
      = - deriv riemannZeta s / riemannZeta s :=
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- **THE LOCAL WEIGHTS ARE NONNEGATIVE, BY ADDRESS.**  Each finite place contributes
`Λ(n)·g(n)` with `Λ(n) ≥ 0`, so a nonnegative test function makes every local term
nonnegative — the positivity of the prime side, term by term, with the weights
exhibited rather than summarised. -/
theorem theLocalWeightsAreNonnegative (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ vonMangoldt n * g n :=
  mul_nonneg vonMangoldt_nonneg (hg n)

/-- And the sum, where it converges. -/
theorem theFinitePlacePairingIsNonnegative {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) :
    0 ≤ ∑' n : ℕ, vonMangoldt n * g n :=
  tsum_nonneg (fun n => theLocalWeightsAreNonnegative g hg n)

end Weil

/-! ## The archimedean place: digamma -/

section Digamma
open Complex

/-- **The digamma function**: the logarithmic derivative of `Γ`.  Mathlib carries `Γ`
and its derivative but no `ψ`; the archimedean term of the explicit formula is written
in `ψ`, so it needs an owner. -/
noncomputable def digamma (s : ℂ) : ℂ := deriv Complex.Gamma s / Complex.Gamma s

/-- **THE DIGAMMA RECURRENCE.**  `ψ(s+1) = ψ(s) + 1/s`, from `Γ(s+1) = s·Γ(s)`
differentiated.  This is the step relation the archimedean term is summed along. -/
theorem theDigammaRecurrence {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) (hs0 : s ≠ 0) :
    digamma (s + 1) = digamma s + 1 / s := by
  have hdG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s hs
  have hGne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hs1 : ∀ m : ℕ, s + 1 ≠ -m := by
    intro m hc
    exact hs (m + 1) (by push_cast at hc ⊢; linear_combination hc)
  have hne : ∀ᶠ z in nhds s, z ≠ 0 := eventually_ne_nhds hs0
  have heq : (fun z : ℂ => z * Complex.Gamma z) =ᶠ[nhds s]
      (fun z : ℂ => Complex.Gamma (z + 1)) := by
    filter_upwards [hne] with z hz
    exact (Complex.Gamma_add_one z hz).symm
  have h1 : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (deriv Complex.Gamma (s + 1)) s := by
    have hbase := (Complex.differentiableAt_Gamma (s + 1) hs1).hasDerivAt
    change HasDerivAt (Complex.Gamma ∘ (fun z : ℂ => z + 1))
      (deriv Complex.Gamma (s + 1)) s
    simpa using hbase.comp s ((hasDerivAt_id s).add_const 1)
  have h2 : HasDerivAt (fun z : ℂ => z * Complex.Gamma z)
      (1 * Complex.Gamma s + s * deriv Complex.Gamma s) s :=
    (hasDerivAt_id s).mul hdG.hasDerivAt
  have h3 : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (1 * Complex.Gamma s + s * deriv Complex.Gamma s) s :=
    h2.congr_of_eventuallyEq heq.symm
  have hkey : deriv Complex.Gamma (s + 1)
      = 1 * Complex.Gamma s + s * deriv Complex.Gamma s := h1.unique h3
  unfold digamma
  rw [hkey, Complex.Gamma_add_one s hs0]
  field_simp
  ring

end Digamma

/-! ## Conjugation -/

section Conj
open Complex Filter Topology

/-- **ZETA CARRIES THE CONJUGATION SYMMETRY ON THE HALF-PLANE.**  Its Dirichlet
coefficients are real, so conjugation passes straight through the series:
`conj(ζ s) = ζ(s̄)` wherever the series converges.  This is the source of the
self-conjugate seam; extending it off the half-plane is the identity theorem. -/
theorem theZetaCarriesTheConjugationSymmetryOnTheHalfPlane {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (riemannZeta s) = riemannZeta ((starRingEnd ℂ) s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_cpow hs, zeta_eq_tsum_one_div_nat_cpow hs']
  rw [Complex.conj_tsum]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by
      intro h; rw [h] at hs; norm_num at hs
    have hcs0 : (starRingEnd ℂ) s ≠ 0 := by
      simpa using hs0
    simp [Complex.zero_cpow hs0, Complex.zero_cpow hcs0]
  · have harg : ((n : ℂ)).arg ≠ Real.pi := by
      have hcast : ((n : ℂ)) = ((n : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact fun hc => Real.pi_ne_zero hc.symm
    rw [map_div₀, map_one, Complex.cpow_conj _ _ harg]
    simp

/-- **THE REFLECTED FUNCTION IS DIFFERENTIABLE.**  If `f` is complex-differentiable at
`s̄` then `z ↦ conj (f (conj z))` is complex-differentiable at `s`, with the conjugated
derivative: conjugation twice restores linearity.  This is the Schwarz reflection
construction, which mathlib does not carry. -/
theorem theReflectedFunctionIsDifferentiable {f : ℂ → ℂ} {f' s : ℂ}
    (hf : HasDerivAt f f' ((starRingEnd ℂ) s)) :
    HasDerivAt (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) f') s := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have hslope : ∀ z : ℂ, slope (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) s z
      = (starRingEnd ℂ) (slope f ((starRingEnd ℂ) s) ((starRingEnd ℂ) z)) := by
    intro z
    unfold slope
    simp [vsub_eq_sub, smul_eq_mul, map_mul, map_sub, map_inv₀]
  rw [show slope (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) s
      = fun z => (starRingEnd ℂ) (slope f ((starRingEnd ℂ) s) ((starRingEnd ℂ) z)) from
    funext hslope]
  refine Filter.Tendsto.comp (Complex.continuous_conj.tendsto _) ?_
  refine hf.comp ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((Complex.continuous_conj.tendsto s).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hc
  refine hz ?_
  have := congrArg (starRingEnd ℂ) hc
  simpa using this

/-- **THE COMPLETED ZETA CARRIES THE SYMMETRY ON THE HALF-PLANE.**  Every factor of
`Λ(s) = π^{−s/2}·Γ(s/2)·Σ n^{−s}` is real-coefficiented or conjugation-equivariant, so
the symmetry holds where the series converges. -/
theorem theCompletedZetaSymmetryOnTheHalfPlane {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (completedRiemannZeta s)
      = completedRiemannZeta ((starRingEnd ℂ) s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [completedZeta_eq_tsum_of_one_lt_re hs, completedZeta_eq_tsum_of_one_lt_re hs']
  have hpi : ((Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_nonneg]
    exact fun hc => Real.pi_ne_zero hc.symm
  have hzeta : (starRingEnd ℂ) (∑' n : ℕ, 1 / (n : ℂ) ^ s)
      = ∑' n : ℕ, 1 / (n : ℂ) ^ ((starRingEnd ℂ) s) := by
    rw [← zeta_eq_tsum_one_div_nat_cpow hs, ← zeta_eq_tsum_one_div_nat_cpow hs']
    exact theZetaCarriesTheConjugationSymmetryOnTheHalfPlane hs
  rw [map_mul, map_mul, hzeta]
  congr 2
  · rw [show (-(starRingEnd ℂ) s / 2) = (starRingEnd ℂ) (-s / 2) from by
      simp [map_div₀, map_ofNat]]
    rw [Complex.cpow_conj _ _ hpi]
    simp
  · rw [← Complex.Gamma_conj]
    congr 1
    simp [map_div₀, map_ofNat]



/-- The entire completed zeta carries the symmetry on the half-plane too: the two poles
it differs by are conjugation-equivariant. -/
theorem theEntireCompletedZetaSymmetryOnTheHalfPlane {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (completedRiemannZeta₀ s)
      = completedRiemannZeta₀ ((starRingEnd ℂ) s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination -h
    rw [this] at hs; norm_num at hs
  have h1 := completedRiemannZeta_eq s
  have h2 := completedRiemannZeta_eq ((starRingEnd ℂ) s)
  have hbase := theCompletedZetaSymmetryOnTheHalfPlane hs
  have hZ0 : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    linear_combination -h1
  have hZ0' : completedRiemannZeta₀ ((starRingEnd ℂ) s)
      = completedRiemannZeta ((starRingEnd ℂ) s) + 1 / ((starRingEnd ℂ) s)
        + 1 / (1 - (starRingEnd ℂ) s) := by
    linear_combination -h2
  rw [hZ0, hZ0', map_add, map_add, hbase, map_div₀, map_div₀, map_one, map_sub, map_one]



/-- **THE COMPLETED ZETA CARRIES THE CONJUGATION SYMMETRY**, everywhere.  The reflected
function is entire by Schwarz reflection, it agrees with `Λ₀` on the half-plane, and the
identity theorem carries the agreement across the whole plane. -/
theorem theCompletedZetaCarriesTheConjugationSymmetry (s : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ s)
      = completedRiemannZeta₀ ((starRingEnd ℂ) s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) z))
    with hgdef
  have hgdiff : Differentiable ℂ g := by
    intro z
    exact (theReflectedFunctionIsDifferentiable
      (differentiable_completedZeta₀ ((starRingEnd ℂ) z)).hasDerivAt).differentiableAt
  have hga : AnalyticOnNhd ℂ g Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hgdiff
  have hZa : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_completedZeta₀
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hev : g =ᶠ[𝓝 (2 : ℂ)] completedRiemannZeta₀ := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [hgdef]
    have := theEntireCompletedZetaSymmetryOnTheHalfPlane (s := (starRingEnd ℂ) z)
      (by simpa using hz)
    simpa using this
  have := hga.eqOn_of_preconnected_of_eventuallyEq hZa isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  have hval := this (Set.mem_univ s)
  rw [hgdef] at hval
  have h2 := congrArg (starRingEnd ℂ) hval
  simpa using h2.symm



/-- **THE COMPLETED ZETA IS REAL ON THE CRITICAL LINE**, unconditionally.  The
functional equation and the conjugation symmetry compose into the anti-linear
involution `s ↦ 1 − s̄`, and on its fixed locus a value must equal its own conjugate. -/
theorem theCompletedZetaIsRealOnTheCriticalLine {s : ℂ} (hs : s.re = 1 / 2) :
    (completedRiemannZeta₀ s).im = 0 := by
  refine theFixedLocusForcesTheValueReal (fun z => ?_) hs
  rw [completedRiemannZeta₀_one_sub, theCompletedZetaCarriesTheConjugationSymmetry]

end Conj

/-! ## The zero set -/

section Strip
open Complex

/-- **THE NONTRIVIAL ZEROS LIE IN THE CRITICAL STRIP.**  Above the strip the Euler
product forbids a zero; below it the functional equation reflects the question back
above, and the only escapes are the negative integers the hypothesis excludes.  This is
the first structural fact about the zero set, and mathlib does not state it. -/
theorem theNontrivialZerosLieInTheCriticalStrip {s : ℂ} (hz : riemannZeta s = 0)
    (hn : ∀ n : ℕ, s ≠ -n) (h1 : s ≠ 1) : 0 ≤ s.re ∧ s.re < 1 := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have hre : 1 < ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hne := riemannZeta_ne_zero_of_one_lt_re hre
    rw [riemannZeta_one_sub hn h1, hz] at hne
    exact hne (by ring)
  · by_contra hge
    push_neg at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- **THE ZERO SET IS DISCRETE.**  Zeta is analytic off its pole, the punctured plane is
connected, and `ζ(2) ≠ 0`, so no zero can be an accumulation point: around every zero
there is a punctured neighbourhood free of zeros.  A zero set that is discrete is a
population that can be *addressed*, which is what a product over it needs. -/
theorem theZeroSetIsDiscrete {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    ∀ᶠ z in nhdsWithin s₀ {s₀}ᶜ, riemannZeta z ≠ 0 := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hconn : IsPreconnected {s : ℂ | s ≠ 1} := by
    have := isConnected_compl_singleton_of_one_lt_rank
      (E := ℂ) (by simp [Complex.rank_real_complex]) 1
    exact this.isPreconnected
  have hana : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    (analyticOnNhd_iff_differentiableOn hopen).mpr
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
  rcases (hana s₀ hs₀).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have h2 : (2 : ℂ) ∈ {s : ℂ | s ≠ 1} := by norm_num
    have hall := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hs₀ hzero
    have := hall h2
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
  · exact hne

/-- **EVERY ZERO CARRIES A FINITE INDEX.**  At a nontrivial zero the vanishing order is
a genuine natural number, not `⊤` — the defect is *localised*, with a multiplicity that
the argument principle counts.  This is Poincaré–Hopf's shape: each defect carries an
index, and the total is what a contour reads. -/
theorem theZeroCarriesAFiniteIndex {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    analyticOrderAt riemannZeta s₀ ≠ ⊤ := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hana : AnalyticAt ℂ riemannZeta s₀ :=
    ((analyticOnNhd_iff_differentiableOn hopen).mpr
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)) s₀ hs₀
  rw [Ne, analyticOrderAt_eq_top]
  intro hzero
  have hconn : IsPreconnected {s : ℂ | s ≠ 1} := by
    have := isConnected_compl_singleton_of_one_lt_rank
      (E := ℂ) (by simp [Complex.rank_real_complex]) 1
    exact this.isPreconnected
  have hana' : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    (analyticOnNhd_iff_differentiableOn hopen).mpr
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
  have hall := hana'.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hs₀ hzero
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num)
    (hall (by norm_num : (2:ℂ) ∈ {s : ℂ | s ≠ 1}))

/-- **THE INDEX IS POSITIVE EXACTLY AT A ZERO.** -/
theorem theIndexIsPositiveExactlyAtAZero {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    riemannZeta s₀ = 0 ↔ analyticOrderAt riemannZeta s₀ ≠ 0 := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hana : AnalyticAt ℂ riemannZeta s₀ :=
    ((analyticOnNhd_iff_differentiableOn hopen).mpr
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)) s₀ hs₀
  constructor
  · intro hz hc
    rw [analyticOrderAt_eq_zero] at hc
    rcases hc with hc | hc
    · exact hc hana
    · exact hc hz
  · intro hne
    by_contra hz
    exact hne (analyticOrderAt_eq_zero.mpr (Or.inr hz))

/-- The punctured plane, where zeta is analytic. -/
def puncturedPlane : Set ℂ := {s : ℂ | s ≠ 1}

theorem theZetaIsAnalyticOffThePole :
    AnalyticOnNhd ℂ riemannZeta puncturedPlane :=
  (analyticOnNhd_iff_differentiableOn isOpen_ne).mpr
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)

/-- **THE ZERO DIVISOR IS THE DEFECT POPULATION.**  Mathlib's divisor of a meromorphic
function is a *locally finite* integer-valued assignment supported on its zeros and
poles — exactly a defect population carrying an index at each address.  For zeta off
its pole, that divisor is supported precisely on the zeros. -/
theorem theZeroDivisorIsSupportedOnTheZeros {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    MeromorphicOn.divisor riemannZeta puncturedPlane s₀ ≠ 0 ↔ riemannZeta s₀ = 0 := by
  have hmer : MeromorphicOn riemannZeta puncturedPlane :=
    theZetaIsAnalyticOffThePole.meromorphicOn
  have hana : AnalyticAt ℂ riemannZeta s₀ := theZetaIsAnalyticOffThePole s₀ hs₀
  rw [MeromorphicOn.divisor_def, if_pos ⟨hmer, hs₀⟩, hana.meromorphicOrderAt_eq]
  constructor
  · intro h
    by_contra hz
    apply h
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]
    simp
  · intro hz
    have hne := (theIndexIsPositiveExactlyAtAZero hs₀).mp hz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (theZeroCarriesAFiniteIndex hs₀)
    rw [← hn] at hne ⊢
    have hn0 : n ≠ 0 := by simpa using hne
    simpa using hn0

/-- **THE DEFECT POPULATION IS DISCRETE.**  The zero divisor's support is a discrete
set: every zero is an isolated address carrying its own index, with no accumulation.
That is what makes a contour able to read a *total* rather than an integral. -/
theorem theZeroDivisorHasDiscreteSupport :
    IsDiscrete (MeromorphicOn.divisor riemannZeta puncturedPlane).support :=
  (MeromorphicOn.divisor riemannZeta puncturedPlane).discreteSupport

end Strip

end Soma.Holonics.RH
