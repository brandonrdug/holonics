import ElementaryHolonics.Millennium.NavierStokesTorusVorticity

/-!
# Parabolic maximum principle for a transported scalar on the periodic space

A scalar `theta` carried by a velocity field `u` on the periodic space and diffused with a
nonnegative viscosity obeys `∂ₜ theta + (u · ∇) theta = nu Δ theta`.  This module proves the
classical parabolic maximum principle for such a scalar on the half-open lifespan `Ico 0 T`: a
one-sided initial bound propagates to every later time, and a two-sided initial bound propagates
in absolute value.  No incompressibility, no bound on `u`, and no positivity of `T` are assumed.

The proof is the standard `ε`-argument.  On the compact cylinder `unitBox ×ˢ Icc 0 t₁` the
penalised scalar `theta - ε t` has a maximum.  If the maximum sits at a positive time, spatial
periodicity makes it a global spatial maximum, so the spatial gradient vanishes and the Laplacian
is nonpositive (a second-derivative test proved here from `C²` regularity), while the one-sided
time derivative is at least `ε`; the transport law forbids this.  Hence the maximum is on the
initial face, and `ε → 0` returns the bound.

**[open]** This owner returns only the maximum principle for an abstract transported scalar.  The
two-dimensional Navier–Stokes regression still owes, beyond this file: the derivation of the
vorticity transport equation from the momentum law of an `OpenPeriodicSolutionOn`; the
z-independence of the solution for z-independent data, which requires the uniqueness receipt;
the vanishing of the third velocity component under that reduction; and the identification of
the bounded scalar with `criticalVorticityRate`.  None of those relations is asserted here.
-/

noncomputable section

open ContDiff Set InnerProductSpace Filter Topology
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesTransportedScalarMaximumPrinciple

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## Second-derivative test at a local maximum -/

/-- [proved-derived; formal-checked] A `C²` real function with a local maximum at `0` has a
nonpositive second derivative there. -/
theorem deriv_deriv_nonpos_of_isLocalMax (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hmax : IsLocalMax g 0) : deriv (deriv g) 0 ≤ 0 := by
  by_contra hpos'
  have hpos : 0 < deriv (deriv g) 0 := not_le.mp hpos'
  have hg' : ContDiff ℝ (1 + 1) g := hg.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 (deriv g) := hg'.deriv'
  have hcont2 : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hd0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < deriv (deriv g) t ∧ g t ≤ g 0 :=
    (hcont2.continuousAt.eventually (lt_mem_nhds hpos)).and hmax
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hmono1 : StrictMonoOn (deriv g) (Ico 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 δ) hg1.continuous.continuousOn
    intro t ht
    rw [interior_Ico] at ht
    exact (hball (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact ht.2)).1
  have hmono0 : StrictMonoOn g (Ico 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 δ) hg.continuous.continuousOn
    intro t ht
    rw [interior_Ico] at ht
    have := hmono1 ⟨le_rfl, hδ⟩ ⟨ht.1.le, ht.2⟩ ht.1
    rwa [hd0] at this
  have hlt : g 0 < g (δ / 2) :=
    hmono0 ⟨le_rfl, hδ⟩ ⟨by positivity, by linarith⟩ (by positivity)
  have hle : g (δ / 2) ≤ g 0 :=
    (hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)).2
  linarith

/-- [proved-derived; formal-checked] Along any direction, the second derivative of a `C²` scalar
field at a local maximum is nonpositive. -/
theorem fderiv_fderiv_apply_self_nonpos_of_isLocalMax (f : Space → ℝ) (hf : ContDiff ℝ 2 f)
    {x₀ : Space} (hmax : IsLocalMax f x₀) (v : Space) :
    fderiv ℝ (fderiv ℝ f) x₀ v v ≤ 0 := by
  let γ : ℝ → Space := fun t => x₀ + t • v
  have hγ : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγ0 : γ 0 = x₀ := by simp [γ]
  have hγderiv : ∀ t, HasDerivAt γ v t := by
    intro t
    have h := ((hasDerivAt_id t).smul_const v).const_add x₀
    rw [one_smul] at h
    exact h
  have hgmax : IsLocalMax (f ∘ γ) 0 := by
    have hmax' : IsLocalMax f (γ 0) := by rwa [hγ0]
    exact hmax'.comp_continuous hγ.continuous.continuousAt
  have hg : ContDiff ℝ 2 (f ∘ γ) := hf.comp hγ
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDfd : Differentiable ℝ (fderiv ℝ f) := hDf.differentiable one_ne_zero
  have hderiv1 : ∀ t, HasDerivAt (f ∘ γ) (fderiv ℝ f (γ t) v) t := fun t =>
    (hfd (γ t)).hasFDerivAt.comp_hasDerivAt t (hγderiv t)
  have hderiv1' : deriv (f ∘ γ) = fun t => fderiv ℝ f (γ t) v :=
    funext fun t => (hderiv1 t).deriv
  have hKv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (γ 0) :=
    (hDfd (γ 0)).clm_apply (differentiableAt_const v)
  have hKv' : fderiv ℝ (fun y => fderiv ℝ f y v) x₀ v = fderiv ℝ (fderiv ℝ f) x₀ v v := by
    rw [fderiv_clm_apply (hDfd x₀) (differentiableAt_const v)]
    simp
  have hderiv2 : HasDerivAt (fun t => fderiv ℝ f (γ t) v) (fderiv ℝ (fderiv ℝ f) x₀ v v) 0 := by
    have := hKv.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hγderiv 0)
    rw [hγ0, hKv'] at this
    exact this
  have hsecond : deriv (deriv (f ∘ γ)) 0 = fderiv ℝ (fderiv ℝ f) x₀ v v := by
    rw [hderiv1']
    exact hderiv2.deriv
  rw [← hsecond]
  exact deriv_deriv_nonpos_of_isLocalMax (f ∘ γ) hg hgmax

/-- [proved-derived; formal-checked] The Laplacian of a `C²` scalar field is nonpositive at a
local maximum. -/
theorem laplacian_nonpos_of_isLocalMax (f : Space → ℝ) (hf : ContDiff ℝ 2 f) {x₀ : Space}
    (hmax : IsLocalMax f x₀) : Δ f x₀ ≤ 0 := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x₀]
  apply Finset.sum_nonpos
  intro i _
  rw [iteratedFDeriv_two_apply]
  exact fderiv_fderiv_apply_self_nonpos_of_isLocalMax f hf hmax
    (EuclideanSpace.basisFun (Fin 3) ℝ i)

/-! ## The compact fundamental cell and its periodic representative -/

/-- [definition] The closed unit cube of the periodic space. -/
def unitBox : Set Space := (EuclideanSpace.equiv (Fin 3) ℝ) ⁻¹' Set.Icc 0 1

/-- [proved-derived; formal-checked] Coordinate description of the unit cube. -/
theorem mem_unitBox_iff {x : Space} : x ∈ unitBox ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  change (0 : Fin 3 → ℝ) ≤ (EuclideanSpace.equiv (Fin 3) ℝ) x ∧
    (EuclideanSpace.equiv (Fin 3) ℝ) x ≤ 1 ↔ _
  rw [Pi.le_def, Pi.le_def]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- [proved-derived; formal-checked] The unit cube is compact. -/
theorem isCompact_unitBox : IsCompact unitBox :=
  (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

/-- [definition] The coordinatewise fractional-part representative of a point. -/
def boxRepresentative (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun i => Int.fract (x i)

@[simp]
theorem boxRepresentative_apply (x : Space) (i : Fin 3) :
    boxRepresentative x i = Int.fract (x i) := rfl

/-- [proved-derived; formal-checked] The representative lies in the unit cube. -/
theorem boxRepresentative_mem_unitBox (x : Space) : boxRepresentative x ∈ unitBox := by
  rw [mem_unitBox_iff]
  intro i
  rw [boxRepresentative_apply]
  exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- [proved-derived; formal-checked] The representative projects to the same torus point. -/
theorem euclideanToSpatialTorus_boxRepresentative (x : Space) :
    euclideanToSpatialTorus (boxRepresentative x) = euclideanToSpatialTorus x := by
  funext i
  change ((Int.fract (x i) : ℝ) : UnitAddCircle) = ((x i : ℝ) : UnitAddCircle)
  have hmod : Int.fract (x i) ≡ x i [PMOD (1 : ℝ)] :=
    AddCommGroup.modEq_iff_eq_add_zsmul.mpr ⟨⌊x i⌋, by simp [Int.fract_add_floor]⟩
  exact AddCommGroup.modEq_iff_eq_mod_zmultiples.mp hmod

/-- [proved-derived; formal-checked] A one-periodic field takes the same value at a point and at
its unit-cube representative. -/
theorem isOnePeriodic_boxRepresentative_eq {F : Type*} (field : Space → F)
    (hperiodic : IsOnePeriodic field) (x : Space) :
    field (boxRepresentative x) = field x :=
  isOnePeriodic_eq_of_euclideanToSpatialTorus_eq field hperiodic
    (euclideanToSpatialTorus_boxRepresentative x)

/-! ## Interior regularity of slices on the open slab -/

/-- [proved-derived; formal-checked] The open slab is a neighbourhood of every event at a strictly
interior time. -/
theorem openSpaceTimeSlab_mem_nhds {T : ℝ} {x : Space} {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    openSpaceTimeSlab T ∈ 𝓝 (x, t) := by
  apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT))
  rintro ⟨y, s⟩ ⟨_, hs⟩
  exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩

/-- [proved-derived; formal-checked] A field `C^n` on the open slab has a `C^n` spatial slice at
every strictly interior time. -/
theorem spatialSlice_contDiff_of_contDiffOn_openSlab {T : ℝ} {n : WithTop ℕ∞}
    (field : Space → ℝ → ℝ)
    (hfield : ContDiffOn ℝ n (Function.uncurry field) (openSpaceTimeSlab T))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ n (fun y => field y t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have huncurry := hfield.contDiffAt (openSpaceTimeSlab_mem_nhds (x := x) ht0 htT)
  have hpair : ContDiffAt ℝ n (fun y : Space => (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def] using huncurry.comp x hpair

/-- [proved-derived; formal-checked] A field `C^n` on the open slab has a `C^n` time section at
every strictly interior time. -/
theorem timeSection_contDiffAt_of_contDiffOn_openSlab {T : ℝ} {n : WithTop ℕ∞}
    (field : Space → ℝ → ℝ)
    (hfield : ContDiffOn ℝ n (Function.uncurry field) (openSpaceTimeSlab T))
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiffAt ℝ n (field x) t := by
  have huncurry := hfield.contDiffAt (openSpaceTimeSlab_mem_nhds (x := x) ht0 htT)
  have hpair : ContDiffAt ℝ n (fun s : ℝ => (x, s)) t :=
    contDiffAt_const.prodMk contDiffAt_id
  simpa [Function.comp_def] using huncurry.comp t hpair

/-! ## The maximum principle -/

/-- [proved-derived; formal-checked] Parabolic maximum principle for a subsolution: a periodic
scalar that is continuous on the open slab, `C²` in space and differentiable in time at every
strictly positive admitted time, and whose transport-diffusion balance is at most `nu Δ` there,
never exceeds its initial upper bound. The law is only required at strictly positive times and
only as an inequality; this is the form consumed by sourced and weighted scalars. -/
theorem transportedSubsolution_le_of_le_at
    {T nu : ℝ} (hnu : 0 ≤ nu) {a : ℝ} (ha : 0 ≤ a)
    (theta : Space → ℝ → ℝ) (u : VelocityField)
    (hcont : ContinuousOn (Function.uncurry theta) (Set.univ ×ˢ Set.Ico a T))
    (hslice : ∀ t ∈ Set.Ioo a T, ContDiff ℝ 2 (fun y => theta y t))
    (htime : ∀ x, ∀ t ∈ Set.Ioo a T, DifferentiableAt ℝ (theta x) t)
    (hperiodic : ∀ t ∈ Set.Ico a T, IsOnePeriodic (fun x => theta x t))
    (hlaw : ∀ x, ∀ t ∈ Set.Ioo a T,
      derivWithin (theta x) (openTimeSlab T) t + fderiv ℝ (fun y => theta y t) x (u x t) ≤
        nu * Δ (fun y => theta y t) x)
    (M : ℝ) (hM : ∀ x, theta x a ≤ M) :
    ∀ x, ∀ t ∈ Set.Ico a T, theta x t ≤ M := by
  intro x₁ t₁ ht₁
  have ht₁0 : a ≤ t₁ := ht₁.1
  have ht₁T : t₁ < T := ht₁.2
  have key : ∀ ε > 0, theta x₁ t₁ ≤ M + ε * (t₁ - a) := by
    intro ε hε
    have hKsub : unitBox ×ˢ Set.Icc a t₁ ⊆ Set.univ ×ˢ Set.Ico a T := by
      rintro ⟨y, s⟩ ⟨_, hs⟩
      exact ⟨Set.mem_univ y, hs.1, lt_of_le_of_lt hs.2 ht₁T⟩
    have hKcompact : IsCompact (unitBox ×ˢ Set.Icc a t₁) := isCompact_unitBox.prod isCompact_Icc
    have hKne : (unitBox ×ˢ Set.Icc a t₁).Nonempty := by
      refine ⟨(0, a), ?_, ?_⟩
      · rw [mem_unitBox_iff]
        intro i
        simp
      · exact ⟨le_rfl, ht₁0⟩
    let F : Space × ℝ → ℝ := fun p => theta p.1 p.2 - ε * p.2
    have hFcont : ContinuousOn F (unitBox ×ˢ Set.Icc a t₁) := by
      have h1 : ContinuousOn (Function.uncurry theta) (unitBox ×ˢ Set.Icc a t₁) :=
        hcont.mono hKsub
      exact h1.sub (continuousOn_const.mul continuous_snd.continuousOn)
    obtain ⟨⟨x₀, t₀⟩, hp₀K, hp₀max⟩ := hKcompact.exists_isMaxOn hKne hFcont
    have hmaxK : ∀ p ∈ unitBox ×ˢ Set.Icc a t₁, F p ≤ F (x₀, t₀) := isMaxOn_iff.mp hp₀max
    have ht₀ : t₀ ∈ Set.Icc a t₁ := hp₀K.2
    have hrep : ∀ y : Space, ∀ s ∈ Set.Icc a t₁, theta y s - ε * s ≤ F (x₀, t₀) := by
      intro y s hs
      have hsT : s ∈ Set.Ico a T := ⟨hs.1, lt_of_le_of_lt hs.2 ht₁T⟩
      have hval : theta (boxRepresentative y) s = theta y s :=
        isOnePeriodic_boxRepresentative_eq (fun z => theta z s) (hperiodic s hsT) y
      have := hmaxK (boxRepresentative y, s) ⟨boxRepresentative_mem_unitBox y, hs⟩
      simpa [F, hval] using this
    have hFle : F (x₀, t₀) ≤ M + -(ε * a) := by
      rcases eq_or_lt_of_le ht₀.1 with h0 | hposa
      · subst h0
        simp only [F]
        linarith [hM x₀]
      · exfalso
        have hpos : 0 < t₀ := lt_of_le_of_lt ha hposa
        have ht₀T : t₀ < T := lt_of_le_of_lt ht₀.2 ht₁T
        have hspatial : IsLocalMax (fun y => theta y t₀) x₀ := by
          apply Filter.Eventually.of_forall
          intro y
          show theta y t₀ ≤ theta x₀ t₀
          have := hrep y t₀ ht₀
          simp only [F] at this
          linarith
        have hsliceAt : ContDiff ℝ 2 (fun y => theta y t₀) := hslice t₀ ⟨hposa, ht₀T⟩
        have hgrad : fderiv ℝ (fun y => theta y t₀) x₀ = 0 := hspatial.fderiv_eq_zero
        have hlap : Δ (fun y => theta y t₀) x₀ ≤ 0 :=
          laplacian_nonpos_of_isLocalMax _ hsliceAt hspatial
        have hdiff : DifferentiableAt ℝ (theta x₀) t₀ := htime x₀ t₀ ⟨hposa, ht₀T⟩
        have hnhds : openTimeSlab T ∈ 𝓝 t₀ :=
          Filter.mem_of_superset (Ioo_mem_nhds hpos ht₀T) Ioo_subset_Ico_self
        have hlaw₀ := hlaw x₀ t₀ ⟨hposa, ht₀T⟩
        rw [derivWithin_of_mem_nhds hnhds, hgrad,
          show ((0 : Space →L[ℝ] ℝ) (u x₀ t₀)) = 0 from rfl, add_zero] at hlaw₀
        have hderiv_nonpos : deriv (theta x₀) t₀ ≤ 0 :=
          hlaw₀.trans (mul_nonpos_of_nonneg_of_nonpos hnu hlap)
        let g : ℝ → ℝ := fun s => theta x₀ s - ε * s
        have hgmax : IsLocalMaxOn g (Set.Iic t₀) t₀ := by
          show ∀ᶠ s in 𝓝[Set.Iic t₀] t₀, g s ≤ g t₀
          rw [eventually_nhdsWithin_iff]
          filter_upwards [Ioi_mem_nhds hposa] with s hs hsle
          have := hrep x₀ s ⟨(Set.mem_Ioi.mp hs).le, le_trans (Set.mem_Iic.mp hsle) ht₀.2⟩
          simpa [g, F] using this
        have hgderiv : HasDerivAt g (deriv (theta x₀) t₀ - ε) t₀ := by
          have h1 := hdiff.hasDerivAt
          have h2 : HasDerivAt (fun s : ℝ => ε * s) ε t₀ := by
            simpa using (hasDerivAt_id t₀).const_mul ε
          exact h1.sub h2
        have hcone : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic t₀) t₀ := by
          apply mem_posTangentConeAt_of_segment_subset
          apply (convex_Iic t₀).segment_subset (Set.mem_Iic.mpr le_rfl)
          rw [Set.mem_Iic]
          linarith
        have hnonpos :=
          hgmax.hasFDerivWithinAt_nonpos hgderiv.hasFDerivAt.hasFDerivWithinAt hcone
        simp at hnonpos
        linarith
    have := hrep x₁ t₁ ⟨ht₁0, le_rfl⟩
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε' : 0 < ε / (t₁ - a + 1) := div_pos hε (by linarith)
  have hbound := key (ε / (t₁ - a + 1)) hε'
  have ht : ε / (t₁ - a + 1) * (t₁ - a) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  linarith

/-- [proved-derived; formal-checked] The subsolution maximum principle from the initial face. -/
theorem transportedSubsolution_le_of_initial_le
    {T nu : ℝ} (hnu : 0 ≤ nu)
    (theta : Space → ℝ → ℝ) (u : VelocityField)
    (hcont : ContinuousOn (Function.uncurry theta) (openSpaceTimeSlab T))
    (hslice : ∀ t ∈ Set.Ioo 0 T, ContDiff ℝ 2 (fun y => theta y t))
    (htime : ∀ x, ∀ t ∈ Set.Ioo 0 T, DifferentiableAt ℝ (theta x) t)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => theta x t))
    (hlaw : ∀ x, ∀ t ∈ Set.Ioo 0 T,
      derivWithin (theta x) (openTimeSlab T) t + fderiv ℝ (fun y => theta y t) x (u x t) ≤
        nu * Δ (fun y => theta y t) x)
    (M : ℝ) (hM : ∀ x, theta x 0 ≤ M) :
    ∀ x, ∀ t ∈ openTimeSlab T, theta x t ≤ M :=
  transportedSubsolution_le_of_le_at hnu le_rfl theta u hcont hslice htime hperiodic hlaw M hM

/-- [proved-derived; formal-checked] Parabolic maximum principle: a periodic scalar transported by
`u` and diffused with nonnegative viscosity on the open lifespan never exceeds its initial upper
bound. -/
theorem transportedScalar_le_of_initial_le
    {T nu : ℝ} (hnu : 0 ≤ nu)
    (theta : Space → ℝ → ℝ) (u : VelocityField)
    (hsmooth : ContDiffOn ℝ 2 (Function.uncurry theta) (openSpaceTimeSlab T))
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => theta x t))
    (hlaw : ∀ x, ∀ t ∈ openTimeSlab T,
      derivWithin (theta x) (openTimeSlab T) t + fderiv ℝ (fun y => theta y t) x (u x t) =
        nu * Δ (fun y => theta y t) x)
    (M : ℝ) (hM : ∀ x, theta x 0 ≤ M) :
    ∀ x, ∀ t ∈ openTimeSlab T, theta x t ≤ M :=
  transportedSubsolution_le_of_initial_le hnu theta u hsmooth.continuousOn
    (fun t ht => spatialSlice_contDiff_of_contDiffOn_openSlab theta hsmooth ht.1 ht.2)
    (fun x t ht =>
      (timeSection_contDiffAt_of_contDiffOn_openSlab theta hsmooth x ht.1 ht.2).differentiableAt
        (by norm_num))
    hperiodic (fun x t ht => (hlaw x t ⟨ht.1.le, ht.2⟩).le) M hM

/-- [proved-derived; formal-checked] **Weighted maximum principle with a multiplicative source,
from an arbitrary initial face `a`.**  If `q` obeys `∂ₜ q + (u · ∇) q ≤ 2 A(t) q + nu Δ q` at every
time in `Ioo a T` and `E` is a positive weight with `E a = 1` and `E' = -2 A E` there, then
`q · E` never exceeds the supremum of `q` on the face `t = a`. -/
theorem transportedSubsolution_mul_weight_le_of_le_at
    {T nu : ℝ} (hnu : 0 ≤ nu) {a : ℝ} (ha : 0 ≤ a)
    (q : Space → ℝ → ℝ) (u : VelocityField) (A E : ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry q) (Set.univ ×ˢ Set.Ico a T))
    (hslice : ∀ t ∈ Set.Ioo a T, ContDiff ℝ 2 (fun y => q y t))
    (htime : ∀ x, ∀ t ∈ Set.Ioo a T, DifferentiableAt ℝ (q x) t)
    (hperiodic : ∀ t ∈ Set.Ico a T, IsOnePeriodic (fun x => q x t))
    (hEcont : Continuous E) (hEpos : ∀ t, 0 < E t) (hEa : E a = 1)
    (hEderiv : ∀ t ∈ Set.Ioo a T, HasDerivAt E (-(2 * A t * E t)) t)
    (hlaw : ∀ x, ∀ t ∈ Set.Ioo a T,
      derivWithin (q x) (openTimeSlab T) t + fderiv ℝ (fun y => q y t) x (u x t) ≤
        2 * A t * q x t + nu * Δ (fun y => q y t) x)
    (M : ℝ) (hM : ∀ x, q x a ≤ M) :
    ∀ x, ∀ t ∈ Set.Ico a T, q x t * E t ≤ M := by
  refine transportedSubsolution_le_of_le_at hnu ha (fun x t => q x t * E t) u ?_ ?_ ?_ ?_ ?_ M ?_
  · show ContinuousOn (fun p : Space × ℝ => q p.1 p.2 * E p.2) (Set.univ ×ˢ Set.Ico a T)
    exact hcont.mul (hEcont.comp continuous_snd).continuousOn
  · intro t ht
    exact (hslice t ht).mul contDiff_const
  · intro x t ht
    exact (htime x t ht).mul (hEderiv t ht).differentiableAt
  · intro t ht x i
    have := hperiodic t ht x i
    simp only at this ⊢
    rw [this]
  · intro x t ht
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have hnhds : openTimeSlab T ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds ht0 ht.2) Ioo_subset_Ico_self
    have hq := hlaw x t ht
    rw [derivWithin_of_mem_nhds hnhds] at hq ⊢
    have hd : HasDerivAt (fun s => q x s * E s)
        (deriv (q x) t * E t + q x t * (-(2 * A t * E t))) t :=
      (htime x t ht).hasDerivAt.mul (hEderiv t ht)
    rw [hd.deriv]
    have hf : fderiv ℝ (fun y => q y t * E t) x = E t • fderiv ℝ (fun y => q y t) x :=
      fderiv_mul_const (((hslice t ht).differentiable (by norm_num)).differentiableAt) (E t)
    have hΔ : Δ (fun y => q y t * E t) x = E t * Δ (fun y => q y t) x := by
      have hfun : (fun y => q y t * E t) = E t • (fun y => q y t) := by
        funext y
        simp [mul_comm]
      rw [hfun, laplacian_smul (E t) (hslice t ht).contDiffAt]
      rfl
    rw [hf, hΔ]
    simp only [smul_apply, smul_eq_mul]
    have hE := hEpos t
    linarith [mul_le_mul_of_nonneg_left hq hE.le]
  · intro x
    simp only [hEa, mul_one]
    exact hM x

/-- [proved-derived; formal-checked] **Weighted maximum principle with a multiplicative source.**
If a periodic scalar `q` obeys `∂ₜ q + (u · ∇) q ≤ 2 A(t) q + nu Δ q` at every strictly positive
admitted time, and `E` is a positive weight with `E 0 = 1` and `E' = -2 A E`, then `q · E` never
exceeds the initial supremum of `q`. With `E t = exp (-2 ∫₀ᵗ A)` this is the exponential bound
`q x t ≤ M · exp (2 ∫₀ᵗ A)`; the source `A` is the receiver-relative rate that the vortex-stretching
term supplies along the vorticity's own frame. -/
theorem transportedSubsolution_mul_weight_le_of_initial_le
    {T nu : ℝ} (hnu : 0 ≤ nu)
    (q : Space → ℝ → ℝ) (u : VelocityField) (A E : ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry q) (openSpaceTimeSlab T))
    (hslice : ∀ t ∈ Set.Ioo 0 T, ContDiff ℝ 2 (fun y => q y t))
    (htime : ∀ x, ∀ t ∈ Set.Ioo 0 T, DifferentiableAt ℝ (q x) t)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => q x t))
    (hEcont : Continuous E) (hEpos : ∀ t, 0 < E t) (hE0 : E 0 = 1)
    (hEderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt E (-(2 * A t * E t)) t)
    (hlaw : ∀ x, ∀ t ∈ Set.Ioo 0 T,
      derivWithin (q x) (openTimeSlab T) t + fderiv ℝ (fun y => q y t) x (u x t) ≤
        2 * A t * q x t + nu * Δ (fun y => q y t) x)
    (M : ℝ) (hM : ∀ x, q x 0 ≤ M) :
    ∀ x, ∀ t ∈ openTimeSlab T, q x t * E t ≤ M := by
  refine transportedSubsolution_le_of_initial_le hnu (fun x t => q x t * E t) u ?_ ?_ ?_ ?_ ?_ M ?_
  · show ContinuousOn (fun p : Space × ℝ => q p.1 p.2 * E p.2) (openSpaceTimeSlab T)
    exact hcont.mul (hEcont.comp continuous_snd).continuousOn
  · intro t ht
    exact (hslice t ht).mul contDiff_const
  · intro x t ht
    exact (htime x t ht).mul (hEderiv t ht).differentiableAt
  · intro t ht x i
    have := hperiodic t ht x i
    simp only at this ⊢
    rw [this]
  · intro x t ht
    have hnhds : openTimeSlab T ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ico_self
    have hq := hlaw x t ht
    rw [derivWithin_of_mem_nhds hnhds] at hq ⊢
    have hd : HasDerivAt (fun s => q x s * E s)
        (deriv (q x) t * E t + q x t * (-(2 * A t * E t))) t :=
      (htime x t ht).hasDerivAt.mul (hEderiv t ht)
    rw [hd.deriv]
    have hf : fderiv ℝ (fun y => q y t * E t) x = E t • fderiv ℝ (fun y => q y t) x :=
      fderiv_mul_const (((hslice t ht).differentiable (by norm_num)).differentiableAt) (E t)
    have hΔ : Δ (fun y => q y t * E t) x = E t * Δ (fun y => q y t) x := by
      have hfun : (fun y => q y t * E t) = E t • (fun y => q y t) := by
        funext y
        simp [mul_comm]
      rw [hfun, laplacian_smul (E t) (hslice t ht).contDiffAt]
      rfl
    rw [hf, hΔ]
    simp only [smul_apply, smul_eq_mul]
    have hE := hEpos t
    linarith [mul_le_mul_of_nonneg_left hq hE.le]
  · intro x
    simp only [hE0, mul_one]
    exact hM x

/-- [proved-derived; formal-checked] Two-sided parabolic maximum principle: a periodic transported
scalar with nonnegative viscosity stays inside its initial absolute bound. -/
theorem abs_transportedScalar_le_of_abs_initial_le
    {T nu : ℝ} (hnu : 0 ≤ nu)
    (theta : Space → ℝ → ℝ) (u : VelocityField)
    (hsmooth : ContDiffOn ℝ 2 (Function.uncurry theta) (openSpaceTimeSlab T))
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => theta x t))
    (hlaw : ∀ x, ∀ t ∈ openTimeSlab T,
      derivWithin (theta x) (openTimeSlab T) t + fderiv ℝ (fun y => theta y t) x (u x t) =
        nu * Δ (fun y => theta y t) x)
    (M : ℝ) (hM : ∀ x, |theta x 0| ≤ M) :
    ∀ x, ∀ t ∈ openTimeSlab T, |theta x t| ≤ M := by
  have hupper := transportedScalar_le_of_initial_le hnu theta u hsmooth hperiodic hlaw M
    (fun x => (le_abs_self _).trans (hM x))
  have hsmooth' : ContDiffOn ℝ 2 (Function.uncurry fun x t => -theta x t)
      (openSpaceTimeSlab T) := hsmooth.neg
  have hperiodic' : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => -theta x t) := by
    intro t ht x i
    show -theta (x + EuclideanSpace.single i 1) t = -theta x t
    rw [show theta (x + EuclideanSpace.single i 1) t = theta x t from hperiodic t ht x i]
  have hlaw' : ∀ x, ∀ t ∈ openTimeSlab T,
      derivWithin (fun s => -theta x s) (openTimeSlab T) t +
        fderiv ℝ (fun y => -theta y t) x (u x t) = nu * Δ (fun y => -theta y t) x := by
    intro x t ht
    have h := hlaw x t ht
    rw [show (fun s => -theta x s) = -(theta x) from rfl, derivWithin.neg,
      show (fun y => -theta y t) = -(fun y => theta y t) from rfl, fderiv_neg, laplacian_neg]
    change -derivWithin (theta x) (openTimeSlab T) t +
      -(fderiv ℝ (fun y => theta y t) x (u x t)) = nu * -(Δ (fun y => theta y t) x)
    linear_combination -h
  have hlower := transportedScalar_le_of_initial_le hnu (fun x t => -theta x t) u hsmooth'
    hperiodic' hlaw' M (fun x => by
      show -theta x 0 ≤ M
      have := abs_le.mp (hM x)
      linarith)
  intro x t ht
  rw [abs_le]
  refine ⟨?_, hupper x t ht⟩
  have : -theta x t ≤ M := hlower x t ht
  linarith

section Audit

#print axioms deriv_deriv_nonpos_of_isLocalMax
#print axioms laplacian_nonpos_of_isLocalMax
#print axioms transportedSubsolution_le_of_le_at
#print axioms transportedSubsolution_le_of_initial_le
#print axioms transportedScalar_le_of_initial_le
#print axioms transportedSubsolution_mul_weight_le_of_le_at
#print axioms transportedSubsolution_mul_weight_le_of_initial_le
#print axioms abs_transportedScalar_le_of_abs_initial_le

end Audit

end Soma.Holonics.Millennium.NavierStokesTransportedScalarMaximumPrinciple
