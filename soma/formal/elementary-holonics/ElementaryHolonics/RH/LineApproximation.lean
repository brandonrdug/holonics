import Mathlib
import ElementaryHolonics.RH.FosterClassHadamard
import ElementaryHolonics.RH.PolyaLine

/-!
# FT4 (iii): a member with its zeros on the seam is the locally uniform limit of seam polynomials

For a member `f` of the Foster class whose zeros all lie on `Re z = ½`, the paired product `P f`
is the square of the product `Qplus f` over the zeros with positive imaginary part, since the
mirror `u ↦ 1 − u` exchanges the two halves and fixes every factor. Hence `f = f(½) · Qplus f`,
and the finite subproducts `f(½) ∏_{i ∈ s} (1 + a i z)` are seam polynomials converging to `f`
locally uniformly. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.LineApproximation

open Complex Metric Set Filter Topology Polynomial
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open Soma.Holonics.RH.FosterClassSplit
open Soma.Holonics.RH.FosterClassHadamard
open Soma.Holonics.RH.PolyaLine
open Soma.Holonics.RH.PolyaStep
open scoped Classical

/-- Every zero lies on the seam. -/
def OnSeam (f : ℂ → ℂ) : Prop := ∀ z, f z = 0 → z.re = 1 / 2

/-- A member with no real zero: every zero has `Im ≠ 0`. This is all the approximation needs. -/
def NoRealZero (f : ℂ → ℂ) : Prop := ∀ z, f z = 0 → z.im ≠ 0

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

theorem f_eq_zero_of_mult_ne_zero {u : ℂ} (hu : mult f u ≠ 0) : f u = 0 := by
  by_contra h
  exact hu (mult_eq_zero_of_ne_zero (f := f) h)

theorem zero_im_ne_zero' (hs : NoRealZero f) (u : Zero f) : ((u : ℂ)).im ≠ 0 :=
  hs u (f_eq_zero_of_mult_ne_zero u.2)

theorem OnSeam.noRealZero (hs : OnSeam f) : NoRealZero f := by
  intro z hz h
  have hre := hs z hz
  have hmult : mult f z ≠ 0 := mult_ne_zero_of_eq_zero (f := f) hz
  apply Zero.ne_half (f := f) ⟨z, hmult⟩
  apply Complex.ext
  · simpa using hre
  · simpa using h

theorem zero_im_ne_zero (hs : OnSeam f) (u : Zero f) : ((u : ℂ)).im ≠ 0 :=
  zero_im_ne_zero' hs.noRealZero u

/-- The upper half of the repeated index. -/
def upper (f : ℂ → ℂ) : Set (Idx f) := {i | 0 < ((i.1 : Zero f) : ℂ).im}

/-- The mirror `u ↦ 1 − u` on the repeated index. -/
def mirror (i : Idx f) : Idx f :=
  ⟨⟨1 - ((i.1 : Zero f) : ℂ), by rw [mult_one_sub (f := f)]; exact i.1.2⟩,
    Fin.cast (by rw [mult_one_sub (f := f)]) i.2⟩

theorem mirror_fst (i : Idx f) : ((mirror i).1 : ℂ) = 1 - ((i.1 : Zero f) : ℂ) := rfl

theorem mirror_mirror (i : Idx f) : mirror (mirror i) = i := by
  apply Sigma.ext
  · apply Subtype.ext
    show 1 - (1 - ((i.1 : Zero f) : ℂ)) = _
    ring
  · rw [Fin.heq_ext_iff]
    · simp [mirror, Fin.coe_cast]
    · show (mult f (1 - (1 - ((i.1 : Zero f) : ℂ)))).toNat = (mult f ((i.1 : Zero f) : ℂ)).toNat
      rw [sub_sub_cancel]

/-- The mirror as a permutation. -/
def mirrorPerm : Equiv.Perm (Idx f) := Function.Involutive.toPerm mirror mirror_mirror

theorem a_mirror (i : Idx f) (z : ℂ) : a (mirror i) z = a i z := by
  unfold a ctr
  rw [mirror_fst, show (1 : ℂ) - ((i.1 : Zero f) : ℂ) - 1 / 2 = -(((i.1 : Zero f) : ℂ) - 1 / 2) by ring,
    div_neg, neg_sq]

theorem mirror_mem_upper_iff' (hs : NoRealZero f) (i : Idx f) : mirror i ∈ upper f ↔ i ∉ upper f := by
  have hne := zero_im_ne_zero' hs i.1
  simp only [upper, mem_setOf_eq, mirror_fst, Complex.sub_im, Complex.one_im, zero_sub, neg_pos]
  constructor
  · intro h1 h2
    linarith
  · intro h
    push_neg at h
    exact lt_of_le_of_ne h hne

/-- The upper half is in bijection with the lower half through the mirror. -/
def upperEquivCompl' (hs : NoRealZero f) : ↥(upper f) ≃ ↥(upper f)ᶜ :=
  Equiv.subtypeEquiv (mirrorPerm (f := f)) (fun i => by
    show i ∈ upper f ↔ mirror i ∈ (upper f)ᶜ
    rw [mem_compl_iff, mirror_mem_upper_iff' hs, not_not])

omit hf in
/-- The half product `Qplus f`. -/
def Qplus (f : ℂ → ℂ) (z : ℂ) : ℂ := ∏' i : ↥(upper f), (1 + a (i : Idx f) z)

theorem hasProd_upper (z : ℂ) :
    HasProd ((fun i : Idx f => 1 + a i z) ∘ (Subtype.val : ↥(upper f) → Idx f)) (Qplus f z) :=
  (multipliable_one_add_of_summable (f := fun i : ↥(upper f) => a (i : Idx f) z)
    ((summable_norm_a (f := f) z).subtype _)).hasProd

theorem hasProd_lower' (hs : NoRealZero f) (z : ℂ) :
    HasProd ((fun i : Idx f => 1 + a i z) ∘ (Subtype.val : ↥(upper f)ᶜ → Idx f)) (Qplus f z) := by
  rw [← Equiv.hasProd_iff (upperEquivCompl' hs)]
  refine (hasProd_upper z).congr_fun ?_
  intro i
  show 1 + a (mirror (i : Idx f)) z = 1 + a (i : Idx f) z
  rw [a_mirror]

/-- **`P f = (Qplus f)²` when the zeros are on the seam.** -/
theorem P_eq_Qplus_sq' (hs : NoRealZero f) (z : ℂ) : P f z = Qplus f z * Qplus f z :=
  ((hasProd_upper z).mul_compl (hasProd_lower' hs z)).tprod_eq

theorem Qplus_half : Qplus f (1 / 2) = 1 := by
  unfold Qplus
  have h : ∀ i : ↥(upper f), 1 + a (i : Idx f) (1 / 2) = 1 := by
    intro i
    simp [a]
  simp only [h]
  exact tprod_one

theorem Qplus_ne_zero {z : ℂ} (hz : mult f z = 0) : Qplus f z ≠ 0 :=
  tprod_one_add_ne_zero_of_summable (fun i => one_add_a_ne_zero (f := f) hz (i : Idx f))
    ((summable_norm_a (f := f) z).subtype _)

theorem hasProdLocallyUniformlyOn_upper (R : ℝ) :
    HasProdLocallyUniformlyOn (fun (i : ↥(upper f)) x => 1 + a (i : Idx f) x) (Qplus f)
      (ball (1 / 2 : ℂ) R) :=
  Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball
    (u := fun i : ↥(upper f) => R ^ 2 * invSq (((i : Idx f).1 : Zero f) : ℂ))
    ((summable_majorant_disc (f := f) R).subtype _)
    (Eventually.of_forall fun i x hx => norm_a_le_of_mem_ball hx (i : Idx f))
    (fun i => (continuous_a (i : Idx f)).continuousOn)

theorem continuous_Qplus : Continuous (Qplus f) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hR : z ∈ ball (1 / 2 : ℂ) (‖z - 1 / 2‖ + 1) := by
    rw [mem_ball, Complex.dist_eq]
    linarith
  have hc : ∀ t : Finset ↥(upper f), ContinuousOn (fun x => ∏ i ∈ t, (1 + a (i : Idx f) x))
      (ball (1 / 2 : ℂ) (‖z - 1 / 2‖ + 1)) := fun t => by
    apply Continuous.continuousOn
    apply continuous_finset_prod (f := fun (i : ↥(upper f)) x => 1 + a (i : Idx f) x) t
    intro i _
    exact continuous_const.add (continuous_a (i : Idx f))
  have h := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_upper (f := f) (‖z - 1 / 2‖ + 1))).continuousOn
    (Eventually.of_forall hc).frequently
  exact h.continuousAt (isOpen_ball.mem_nhds hR)

/-- **`f = f(½) · Qplus f` when the zeros are on the seam.** -/
theorem eq_centre_mul_Qplus' (hs : NoRealZero f) : f = fun z => f (1 / 2) * Qplus f z := by
  have hU : EqOn f (fun z => f (1 / 2) * Qplus f z) (U f) := by
    apply IsPreconnected.eq_of_sq_eq (isPreconnected_U (f := f)) hf.diff.continuous.continuousOn
      (continuous_const.mul continuous_Qplus).continuousOn
    · intro z hz
      simp only [Pi.pow_apply, Pi.mul_apply]
      rw [sq_eq_centre_mul_P (f := f), P_eq_Qplus_sq' hs]
      ring
    · intro z hz
      exact mul_ne_zero hf.centre (Qplus_ne_zero (mult_eq_zero_of_ne_zero (f := f) hz))
    · exact half_mem_U (f := f)
    · show f (1 / 2) = f (1 / 2) * Qplus f (1 / 2)
      rw [Qplus_half (f := f), mul_one]
  apply Continuous.ext_on (Set.Countable.dense_compl ℝ (zeroSet_countable (f := f)))
    hf.diff.continuous (continuous_const.mul continuous_Qplus)
  rw [← U_eq_compl]
  exact hU

/-- The finite approximant over a finset of the upper half. -/
def approx (s : Finset ↥(upper f)) (z : ℂ) : ℂ := f (1 / 2) * ∏ i ∈ s, (1 + a (i : Idx f) z)

/-- **The approximants converge to `f` locally uniformly.** -/
theorem tendsto_approx' (hs : NoRealZero f) :
    TendstoLocallyUniformly (approx (f := f)) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (1 / 2 : ℂ)
  have hKb : K ⊆ ball (1 / 2 : ℂ) (R + 1) :=
    hR.trans (closedBall_subset_ball (by linarith))
  have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
    (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      (hasProdLocallyUniformlyOn_upper (f := f) (R + 1))) K hKb hK
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hc : 0 < ‖f (1 / 2 : ℂ)‖ + 1 := by positivity
  filter_upwards [h (ε / (‖f (1 / 2 : ℂ)‖ + 1)) (by positivity)] with s hs' z hz
  have hfz : f z = f (1 / 2) * Qplus f z := congrFun (eq_centre_mul_Qplus' hs) z
  rw [hfz]
  unfold approx
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have h1 := hs' z hz
  rw [dist_eq_norm] at h1
  calc ‖f (1 / 2)‖ * ‖Qplus f z - ∏ i ∈ s, (1 + a (i : Idx f) z)‖
      ≤ (‖f (1 / 2)‖ + 1) * ‖Qplus f z - ∏ i ∈ s, (1 + a (i : Idx f) z)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith
    _ < (‖f (1 / 2)‖ + 1) * (ε / (‖f (1 / 2)‖ + 1)) := by
        apply mul_lt_mul_of_pos_left h1 hc
    _ = ε := by field_simp

/-! ### The seam forms, as before -/

theorem mirror_mem_upper_iff (hs : OnSeam f) (i : Idx f) : mirror i ∈ upper f ↔ i ∉ upper f :=
  mirror_mem_upper_iff' hs.noRealZero i

def upperEquivCompl (hs : OnSeam f) : ↥(upper f) ≃ ↥(upper f)ᶜ := upperEquivCompl' hs.noRealZero

theorem hasProd_lower (hs : OnSeam f) (z : ℂ) :
    HasProd ((fun i : Idx f => 1 + a i z) ∘ (Subtype.val : ↥(upper f)ᶜ → Idx f)) (Qplus f z) :=
  hasProd_lower' hs.noRealZero z

theorem P_eq_Qplus_sq (hs : OnSeam f) (z : ℂ) : P f z = Qplus f z * Qplus f z :=
  P_eq_Qplus_sq' hs.noRealZero z

theorem eq_centre_mul_Qplus (hs : OnSeam f) : f = fun z => f (1 / 2) * Qplus f z :=
  eq_centre_mul_Qplus' hs.noRealZero

theorem tendsto_approx (hs : OnSeam f) :
    TendstoLocallyUniformly (approx (f := f)) f atTop :=
  tendsto_approx' hs.noRealZero

/-! ## The approximants are seam polynomials -/

/-- The height of an upper zero. -/
def γ (i : ↥(upper f)) : ℝ := (((i : Idx f).1 : Zero f) : ℂ).im

theorem γ_pos (i : ↥(upper f)) : 0 < γ i := i.2

theorem ctr_eq (hs : OnSeam f) (i : ↥(upper f)) : ctr (i : Idx f) = (γ i : ℂ) * I := by
  unfold ctr γ
  have hre := hs _ (f_eq_zero_of_mult_ne_zero ((i : Idx f).1).2)
  apply Complex.ext
  · simp [hre]
  · simp

/-- The real polynomial of a finset of upper zeros: `∏ (1 − X²/γ²)`. -/
def qpoly (s : Finset ↥(upper f)) : ℝ[X] :=
  ∏ i ∈ s, (C 1 - C ((γ i)⁻¹ ^ 2) * X ^ 2)

theorem approx_eq_seamPoly (hs : OnSeam f) (s : Finset ↥(upper f)) (z : ℂ) :
    approx s z = f (1 / 2) * seamPoly (qpoly s) z := by
  unfold approx seamPoly qpoly
  congr 1
  rw [Polynomial.map_prod, eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  unfold a
  rw [ctr_eq hs]
  have hγ : (γ i : ℂ) ≠ 0 := by exact_mod_cast (γ_pos i).ne'
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  simp only [div_pow, mul_pow, neg_sq, Complex.I_sq]
  field_simp
  ring

theorem qpoly_ne_zero (s : Finset ↥(upper f)) : qpoly s ≠ 0 := by
  unfold qpoly
  rw [Finset.prod_ne_zero_iff]
  intro i _
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp at this

theorem nonreal_qpoly (s : Finset ↥(upper f)) : nonreal (qpoly s) = 0 := by
  rw [nonreal_eq_card_filter, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro w hw
  have hmap : (qpoly s).map ofRealHom ≠ 0 := by
    intro h
    exact qpoly_ne_zero s ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp h)
  rw [mem_roots hmap, IsRoot, qpoly, Polynomial.map_prod, eval_prod, Finset.prod_eq_zero_iff] at hw
  obtain ⟨i, _, hi⟩ := hw
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hi
  have hγ : (γ i : ℂ) ≠ 0 := by exact_mod_cast (γ_pos i).ne'
  -- w² = γ², so w = ±γ, real
  have hsq : w ^ 2 = (γ i : ℂ) ^ 2 := by
    simp only [Complex.ofRealHom_eq_coe] at hi
    push_cast at hi
    have h2 : (γ i : ℂ) ^ 2 * (1 - ((γ i : ℂ))⁻¹ ^ 2 * w ^ 2) = 0 := by rw [hi, mul_zero]
    have h3 : (γ i : ℂ) ^ 2 * ((γ i : ℂ))⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hγ, one_pow]
    linear_combination -h2 - w ^ 2 * h3
  have : (w - γ i) * (w + γ i) = 0 := by ring_nf; linear_combination hsq
  push_neg
  rcases mul_eq_zero.mp this with h | h
  · rw [sub_eq_zero] at h
    rw [h]
    simp
  · rw [add_eq_zero_iff_eq_neg] at h
    rw [h]
    simp

end Soma.Holonics.RH.LineApproximation
