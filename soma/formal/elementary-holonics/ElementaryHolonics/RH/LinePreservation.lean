import Mathlib
import ElementaryHolonics.RH.LineApproximation
import ElementaryHolonics.RH.EulerIterates
import ElementaryHolonics.RH.HurwitzLine
import ElementaryHolonics.RH.FosterClassHeatFlow
import ElementaryHolonics.RH.KernelFlow
import ElementaryHolonics.RH.RealZeroTimes

/-!
# FT4 (iii)–(v): forward preservation at the entire face, and `RH ⟺ Λ_DN ≤ 0`

For a member `f` of the Foster class with its zeros on the seam, the Euler iterates of its seam
polynomial approximants have seam zeros (`PolyaLine`), converge to the Euler iterates of `f`
(derivatives of locally uniform limits), which therefore have seam zeros by Hurwitz, and converge
to `heatE (−λ) f` (`EulerIterates`), which therefore has seam zeros by Hurwitz: **the flow never
creates a pair** — in the tree's coordinate `τ = −t`, the seam times are an up-set (standard
de Bruijn–Newman time is `4τ`). With their
closedness (`RealZeroTimes`) this gives `RH ⟺ Λ_DN ≤ 0` whenever a seam time exists. Every
theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.LinePreservation

open Complex Metric Set Filter Topology Finset
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open Soma.Holonics.RH.FosterClassHadamard
open Soma.Holonics.RH.PolyaLine
open Soma.Holonics.RH.PolyaStep
open Soma.Holonics.RH.LineApproximation
open Soma.Holonics.RH.EulerIterates
open Soma.Holonics.RH.HurwitzLine
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatEquationEntire
open Soma.Holonics.RH.KernelFlow
open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.FosterClassHeatFlow
open scoped Classical

/-! ## Locally uniform limits: derivatives, constants, finite sums -/

theorem tendstoLocallyUniformly_iteratedDeriv {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hlim : TendstoLocallyUniformly F G l) (m : ℕ) :
    TendstoLocallyUniformly (fun n => iteratedDeriv m (F n)) (iteratedDeriv m G) l := by
  induction m with
  | zero => simpa using hlim
  | succ m ih =>
    have h := (tendstoLocallyUniformlyOn_univ.mpr ih).deriv
      (Eventually.of_forall fun n => (differentiable_iteratedDeriv (hF n) m).differentiableOn)
      isOpen_univ
    rw [tendstoLocallyUniformlyOn_univ] at h
    simp only [iteratedDeriv_succ]
    exact h

theorem tendstoLocallyUniformly_const_mul {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {G : ℂ → ℂ}
    (hlim : TendstoLocallyUniformly F G l) (c : ℂ) :
    TendstoLocallyUniformly (fun n z => c * F n z) (fun z => c * G z) l := by
  rw [Metric.tendstoLocallyUniformly_iff] at hlim ⊢
  intro ε hε x
  obtain ⟨t, ht, hev⟩ := hlim (ε / (‖c‖ + 1)) (by positivity) x
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev] with n hn y hy
  have h := hn y hy
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  rw [dist_eq_norm] at h
  calc ‖c‖ * ‖G y - F n y‖ ≤ (‖c‖ + 1) * ‖G y - F n y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith
    _ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) := by
        apply mul_lt_mul_of_pos_left h (by positivity)
    _ = ε := by field_simp

theorem tendstoLocallyUniformly_zero {ι : Type*} {l : Filter ι} :
    TendstoLocallyUniformly (fun (_ : ι) (_ : ℂ) => (0 : ℂ)) (fun _ => 0) l := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  exact ⟨univ, univ_mem, Eventually.of_forall fun n y _ => by simpa using hε⟩

theorem tendstoLocallyUniformly_finset_sum {ι κ : Type*} {l : Filter ι} (s : Finset κ)
    {F : κ → ι → ℂ → ℂ} {G : κ → ℂ → ℂ} (h : ∀ k ∈ s, TendstoLocallyUniformly (F k) (G k) l) :
    TendstoLocallyUniformly (fun n z => ∑ k ∈ s, F k n z) (fun z => ∑ k ∈ s, G k z) l := by
  induction s using Finset.induction_on with
  | empty => simpa using tendstoLocallyUniformly_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    exact h1.add h2

/-! ## The Euler iterate is linear and entire -/

theorem differentiable_eulerIter {g : ℂ → ℂ} (hg : Differentiable ℂ g) (lam : ℝ) (N : ℕ) :
    Differentiable ℂ (eulerIter lam N g) := by
  unfold eulerIter
  have hfun : (fun z : ℂ => ∑ k ∈ range (N + 1),
      ((N.choose k : ℂ) * ((lam : ℂ) / N) ^ k) * iteratedDeriv (2 * k) g z) =
      ∑ k ∈ range (N + 1), (fun z : ℂ => ((N.choose k : ℂ) * ((lam : ℂ) / N) ^ k) *
        iteratedDeriv (2 * k) g z) := by
    funext z
    rw [Finset.sum_apply]
  rw [hfun]
  apply Differentiable.sum
  intro k _
  exact (differentiable_iteratedDeriv hg (2 * k)).const_mul _

theorem eulerIter_const_mul {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) (lam : ℝ) (N : ℕ) (z : ℂ) :
    eulerIter lam N (fun w => c * g w) z = c * eulerIter lam N g z := by
  unfold eulerIter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDeriv_const_mul c (hg.contDiff.contDiffAt)]
  ring

theorem tendstoLocallyUniformly_eulerIter {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hlim : TendstoLocallyUniformly F G l) (lam : ℝ) (N : ℕ) :
    TendstoLocallyUniformly (fun n => eulerIter lam N (F n)) (eulerIter lam N G) l := by
  unfold eulerIter
  apply tendstoLocallyUniformly_finset_sum
  intro k _
  exact tendstoLocallyUniformly_const_mul (tendstoLocallyUniformly_iteratedDeriv hF hG hlim (2 * k)) _

/-! ## Forward preservation for a member with seam zeros -/

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-- The zeros of a member are countable, as a type. -/
instance instCountableZero : Countable (Zero f) := by
  have h : {u : ℂ | mult f u ≠ 0}.Countable :=
    (zeroSet_countable (f := f)).mono fun u hu => f_eq_zero_of_mult_ne_zero (f := f) hu
  exact h.to_subtype

/-- The Euler iterate of an approximant has its zeros on the seam. -/
theorem eulerIter_approx_re (hs : OnSeam f) {lam : ℝ} (hlam : 0 ≤ lam) (N : ℕ)
    (s : Finset ↥(upper f)) {z : ℂ} (hz : eulerIter lam N (approx s) z = 0) : z.re = 1 / 2 := by
  have hfun : approx (f := f) s = fun w => f (1 / 2) * seamPoly (qpoly s) w :=
    funext (approx_eq_seamPoly hs s)
  rw [hfun, eulerIter_const_mul (differentiable_seamPoly _)] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hf.centre
  · exact eulerIter_seamPoly_re hlam N (qpoly_ne_zero s) (nonreal_qpoly s) h

theorem differentiable_approx (s : Finset ↥(upper f)) : Differentiable ℂ (approx (f := f) s) := by
  unfold approx
  apply Differentiable.const_mul
  have : (fun z : ℂ => ∏ i ∈ s, (1 + a (i : Idx f) z)) = ∏ i ∈ s, (fun z => 1 + a (i : Idx f) z) := by
    funext z
    rw [Finset.prod_apply]
  rw [this]
  apply Differentiable.finset_prod
  intro i _
  exact (differentiable_const _).add (differentiable_a (i : Idx f))

/-- The Euler iterate of `f` has its zeros on the seam, unless it vanishes. -/
theorem eulerIter_re (hs : OnSeam f) {lam : ℝ} (hlam : 0 ≤ lam) (N : ℕ)
    (hne : ∃ x, eulerIter lam N f x ≠ 0) : ∀ z, eulerIter lam N f z = 0 → z.re = 1 / 2 :=
  zeros_on_seam (l := atTop) (F := fun s => eulerIter lam N (approx s)) (G := eulerIter lam N f)
    (Eventually.of_forall fun s => differentiable_eulerIter (differentiable_approx s) lam N)
    (differentiable_eulerIter hf.diff lam N)
    (tendstoLocallyUniformly_eulerIter (fun s => differentiable_approx s) hf.diff
      (tendsto_approx hs) lam N)
    hne (Eventually.of_forall fun s z hz => eulerIter_approx_re hs hlam N s hz)

/-- **Forward preservation for a member**: `heatE (−λ) f` has its zeros on the seam for `λ ≥ 0`,
unless it vanishes. -/
theorem onSeam_heatE_neg (hs : OnSeam f) {lam : ℝ} (hlam : 0 ≤ lam)
    (hne : ∃ x, heatE (-lam) f x ≠ 0) : OnSeam (heatE (-lam) f) := by
  have hlim := tendsto_eulerIter hf.diff hf.growth hf.A_pos.le hf.B_nonneg hf.σ_pos hf.σ_lt_two hlam
  apply zeros_on_seam (l := atTop) (F := fun N => eulerIter lam N f) (G := heatE (-lam) f)
    (Eventually.of_forall fun N => differentiable_eulerIter hf.diff lam N)
    (differentiable_heatE hf.diff hf.growth hf.A_pos.le hf.B_nonneg hf.σ_pos hf.σ_lt_two _)
    hlim hne
  obtain ⟨x, hx⟩ := hne
  have hpt : Tendsto (fun N => eulerIter lam N f x) atTop (𝓝 (heatE (-lam) f x)) :=
    (tendstoLocallyUniformlyOn_univ.mpr hlim).tendsto_at (mem_univ x)
  filter_upwards [hpt.eventually_ne hx] with N hN
  exact eulerIter_re hs hlam N ⟨x, hN⟩

/-! ## The flow of `ξ`: the seam times are an up-set -/

omit hf in
/-- **The flow never creates a pair**: the seam times are an up-set in the tree's coordinate. -/
theorem seamTimes_upset {τ τ' : ℝ} (hτ : τ ∈ seamTimes) (h : τ ≤ τ') : τ' ∈ seamTimes := by
  have hsemi : heatE (-τ') riemannXi = heatE (-(τ' - τ)) (heatE (-τ) riemannXi) := by
    rw [heatE_heatE_riemannXi]
    congr 1
    ring
  intro z hz
  rw [hsemi] at hz
  have hne : ∃ x, heatE (-(τ' - τ)) (heatE (-τ) riemannXi) x ≠ 0 :=
    ⟨1 / 2, by rw [← hsemi]; exact heatE_riemannXi_half_ne_zero _⟩
  exact onSeam_heatE_neg (f := heatE (-τ) riemannXi) hτ (by linarith) hne z hz

omit hf in
/-- **`RH ⟺ Λ_DN ≤ 0`**, given a seam time. -/
theorem riemannHypothesis_iff_Λ_DN_le (hne : seamTimes.Nonempty) : RiemannHypothesis ↔ Λ_DN ≤ 0 :=
  RealZeroTimes.riemannHypothesis_iff_Λ_DN_le hne (fun τ hτ τ' h => seamTimes_upset hτ h)

end Soma.Holonics.RH.LinePreservation
