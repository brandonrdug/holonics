import Mathlib
import ElementaryHolonics.RH.LineApproximation
import ElementaryHolonics.RH.ConjugationEntire

/-!
# DB3 (iii): the conjugation involution on the upper zeros

For a member `f` of the Foster class with `f(z̄) = conj f(z)`, the zero multiplicities are
conjugation-invariant, so `u ↦ 1 − ū` is an involution `σ` of the repeated upper index. The
symmetric closure `sym s = s ∪ σ s` of a finset is `σ`-invariant, cofinal, and a product over it
can be reindexed by `σ`. The factor of `σ i` is the conjugate factor: `a (σ i) z = conj (a i z̄)`.
-/

noncomputable section

namespace Soma.Holonics.RH.ConjIndex

open Complex ComplexConjugate Set Filter Topology
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open Soma.Holonics.RH.LineApproximation
open Soma.Holonics.RH.ConjugationEntire

/-- Conjugation symmetry. -/
def ConjSymm (f : ℂ → ℂ) : Prop := ∀ z, f (conj z) = conj (f z)

theorem analyticAt_conj_conj {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g (conj z)) :
    AnalyticAt ℂ (fun w => conj (g (conj w))) z := by
  have ht : Tendsto (fun w : ℂ => conj w) (𝓝 z) (𝓝 (conj z)) :=
    Complex.continuous_conj.continuousAt
  have hev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ g (conj w) := ht.eventually hg.eventually_analyticAt
  obtain ⟨U, hU, hUan⟩ := Filter.eventually_iff_exists_mem.mp hev
  refine DifferentiableOn.analyticAt (s := U) (fun w hw => ?_) hU
  exact (hasDerivAt_conj_conj (hUan w hw).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

theorem analyticOrderAt_conj (hc : ConjSymm f) (u : ℂ) :
    analyticOrderAt f (conj u) = analyticOrderAt f u := by
  have hu := hf.analyticAt u
  have hcu := hf.analyticAt (conj u)
  have hf' : ∀ w, f w = conj (f (conj w)) := fun w => by rw [hc, Complex.conj_conj]
  have ht : Tendsto (fun w : ℂ => conj w) (𝓝 (conj u)) (𝓝 u) := by
    have := Complex.continuous_conj.continuousAt (x := conj u)
    rw [ContinuousAt, Complex.conj_conj] at this
    exact this
  by_cases htop : analyticOrderAt f u = ⊤
  · rw [htop, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at htop
    filter_upwards [ht.eventually htop] with w hw
    rw [hf' w, hw, map_zero]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn]
    obtain ⟨g, hg, hg0, hev⟩ := hu.analyticOrderAt_eq_natCast.mp hn.symm
    rw [hcu.analyticOrderAt_eq_natCast]
    refine ⟨fun w => conj (g (conj w)), analyticAt_conj_conj (by rwa [Complex.conj_conj]), ?_, ?_⟩
    · simpa using hg0
    · filter_upwards [ht.eventually hev] with w hw
      rw [hf' w, hw]
      simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

theorem mult_conj (hc : ConjSymm f) (u : ℂ) : mult f (conj u) = mult f u := by
  unfold mult
  rw [(hf.analyticAt _).meromorphicOrderAt_eq, (hf.analyticAt _).meromorphicOrderAt_eq,
    analyticOrderAt_conj hc]

/-! ## The involution -/

/-- The conjugate on the repeated index. -/
def conjIdx (hc : ConjSymm f) (i : Idx f) : Idx f :=
  ⟨⟨conj ((i.1 : Zero f) : ℂ), by rw [mult_conj hc]; exact i.1.2⟩,
    Fin.cast (by rw [mult_conj hc]) i.2⟩

theorem conjIdx_fst (hc : ConjSymm f) (i : Idx f) :
    ((conjIdx hc i).1 : ℂ) = conj ((i.1 : Zero f) : ℂ) := rfl

/-- `u ↦ 1 − ū`: the mirror of the conjugate. -/
def refl (hc : ConjSymm f) (i : Idx f) : Idx f := mirror (conjIdx hc i)

theorem refl_fst (hc : ConjSymm f) (i : Idx f) :
    ((refl hc i).1 : ℂ) = 1 - conj ((i.1 : Zero f) : ℂ) := rfl

theorem refl_refl (hc : ConjSymm f) (i : Idx f) : refl hc (refl hc i) = i := by
  apply Sigma.ext
  · apply Subtype.ext
    show 1 - conj (1 - conj ((i.1 : Zero f) : ℂ)) = _
    rw [map_sub, map_one, Complex.conj_conj]
    ring
  · rw [Fin.heq_ext_iff]
    · first | rfl | simp [refl, mirror, conjIdx, Fin.coe_cast]
    · show (mult f (1 - conj (1 - conj ((i.1 : Zero f) : ℂ)))).toNat =
        (mult f ((i.1 : Zero f) : ℂ)).toNat
      rw [map_sub, map_one, Complex.conj_conj, sub_sub_cancel]

theorem refl_im (hc : ConjSymm f) (i : Idx f) :
    (((refl hc i).1 : Zero f) : ℂ).im = ((i.1 : Zero f) : ℂ).im := by
  rw [refl_fst]
  simp

theorem refl_mem_upper_iff (hc : ConjSymm f) (i : Idx f) : refl hc i ∈ upper f ↔ i ∈ upper f := by
  simp only [LineApproximation.upper, mem_setOf_eq, refl_im]

/-- The involution on the upper index. -/
def σ' (hc : ConjSymm f) (i : ↥(upper f)) : ↥(upper f) :=
  ⟨refl hc i, (refl_mem_upper_iff hc i).mpr i.2⟩

theorem σ'_σ' (hc : ConjSymm f) (i : ↥(upper f)) : σ' hc (σ' hc i) = i := by
  apply Subtype.ext
  show refl hc (refl hc (i : Idx f)) = i
  exact refl_refl hc i

theorem ctr_conjIdx (hc : ConjSymm f) (i : Idx f) : ctr (conjIdx hc i) = conj (ctr i) := by
  simp only [ctr, conjIdx_fst]
  rw [map_sub, map_div₀, map_one, map_ofNat]

/-- The factor of the reflected index is the conjugate factor. -/
theorem a_refl (hc : ConjSymm f) (i : Idx f) (z : ℂ) : a (refl hc i) z = conj (a i (conj z)) := by
  unfold refl
  rw [a_mirror]
  simp only [a, ctr_conjIdx]
  rw [map_neg, map_pow, map_div₀, map_sub, Complex.conj_conj, map_div₀, map_one, map_ofNat]

theorem a_σ' (hc : ConjSymm f) (i : ↥(upper f)) (z : ℂ) :
    a ((σ' hc i : ↥(upper f)) : Idx f) z = conj (a (i : Idx f) (conj z)) :=
  a_refl hc i z

/-! ## Symmetric finsets -/

/-- The `σ`-closure of a finset. -/
def sym (hc : ConjSymm f) (s : Finset ↥(upper f)) : Finset ↥(upper f) :=
  s ∪ s.image (σ' hc)

theorem subset_sym (hc : ConjSymm f) (s : Finset ↥(upper f)) : s ⊆ sym hc s :=
  Finset.subset_union_left

theorem tendsto_sym (hc : ConjSymm f) : Tendsto (sym hc) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun a hba => hba.trans (subset_sym hc a)⟩

theorem σ'_mem_sym_iff (hc : ConjSymm f) (s : Finset ↥(upper f)) (i : ↥(upper f)) :
    σ' hc i ∈ sym hc s ↔ i ∈ sym hc s := by
  simp only [sym, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨j, hj, hji⟩)
    · exact Or.inr ⟨σ' hc i, h, σ'_σ' hc i⟩
    · left
      have := congrArg (σ' hc) hji
      rw [σ'_σ', σ'_σ'] at this
      rw [← this]
      exact hj
  · rintro (h | ⟨j, hj, hji⟩)
    · exact Or.inr ⟨i, h, rfl⟩
    · left
      rw [← hji, σ'_σ']
      exact hj

/-- A product over a symmetric finset can be reindexed by `σ`. -/
theorem prod_sym_σ' (hc : ConjSymm f) (s : Finset ↥(upper f)) (F : ↥(upper f) → ℝ) :
    ∏ i ∈ sym hc s, F (σ' hc i) = ∏ i ∈ sym hc s, F i := by
  apply Finset.prod_nbij' (σ' hc) (σ' hc)
  · intro i hi
    exact (σ'_mem_sym_iff hc s i).mpr hi
  · intro i hi
    exact (σ'_mem_sym_iff hc s i).mpr hi
  · intro i _
    exact σ'_σ' hc i
  · intro i _
    exact σ'_σ' hc i
  · intro i _
    rfl

end Soma.Holonics.RH.ConjIndex
