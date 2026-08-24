import Mathlib.Analysis.InnerProductSpace.ProdL2
import ElementaryHolonics.Millennium.HilbertTransportRefinement

/-!
# An unbounded incidence-bearing Hilbert refinement chain

This file replaces the dimension-two identity--zero calibration by a sequential family whose
middle dimension is unbounded and whose two boundary maps are both nonzero.  At scale `n` the
complex is the split exact chain

```text
Vₙ  --x ↦ (x,0)-->  Vₙ ⊕₂ Vₙ  --(x,y) ↦ y-->  Vₙ,
```

where `Vₙ = EuclideanSpace ℝ (Fin (n+1))`.  The adjacent refinement appends one zero coordinate
and acts on both middle summands.  Both differential and adjoint squares commute.

The middle Hodge Laplacian is the identity, so the complete non-harmonic population has the exact
scale-uniform gap `1` even though the carrier dimension is unbounded.  This is a useful control:
unbounded refinement and nonzero incidence do not by themselves create a vanishing-gap sequence.
The chain is still split linear algebra, not a lattice gauge-field configuration space, an
interacting Yang--Mills Hamiltonian, or a continuum limit.

Truth status: the constructions are `definition`; the theorems are `proved-derived`; a nonlinear
gauge realization, continuum reconstruction, and the Yang--Mills mass gap remain `open`.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.Coupling

universe u

/-! ## The split incidence complex -/

/-- Isometric inclusion into the first summand of the Hilbert direct sum. -/
def splitFirstInclusion (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    V →ₗᵢ[ℝ] WithLp 2 (V × V) where
  toLinearMap :=
    { toFun := fun x ↦ WithLp.toLp 2 (x, 0)
      map_add' := by
        intro x y
        apply WithLp.ofLp_injective
        simp
      map_smul' := by
        intro c x
        apply WithLp.ofLp_injective
        simp }
  norm_map' := by
    intro x
    exact WithLp.norm_toLp_fst 2 V V x

/-- The split exact Hilbert chain `V → V ⊕₂ V → V`. -/
def splitIncidenceComplex (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    FiniteHilbertTransportComplex where
  Left := V
  Middle := WithLp 2 (V × V)
  Right := V
  chain :=
    { into := (splitFirstInclusion V).toContinuousLinearMap
      outOf := WithLp.sndL 2 ℝ V V
      composite_zero := by
        intro x
        rfl }

/-- The incoming adjoint is projection to the first summand. -/
theorem splitIncidenceComplex_incomingAdjoint
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (x : WithLp 2 (V × V)) :
    (splitIncidenceComplex V).chain.incomingAdjoint x = x.fst := by
  apply ext_inner_left ℝ
  intro y
  rw [HilbertTransportChain.incomingAdjoint,
    ContinuousLinearMap.adjoint_inner_right]
  simp [splitIncidenceComplex, splitFirstInclusion, WithLp.prod_inner_apply]

/-- The outgoing adjoint inserts into the second summand. -/
theorem splitIncidenceComplex_outgoingAdjoint
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (x : V) :
    (splitIncidenceComplex V).chain.outgoingAdjoint x = WithLp.toLp 2 (0, x) := by
  apply ext_inner_right ℝ
  intro y
  rw [HilbertTransportChain.outgoingAdjoint,
    ContinuousLinearMap.adjoint_inner_left]
  simp [splitIncidenceComplex, WithLp.prod_inner_apply]

/-- The split chain's middle Hodge Laplacian is exactly the identity. -/
theorem splitIncidenceComplex_middleLaplacian
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (x : WithLp 2 (V × V)) :
    (splitIncidenceComplex V).chain.middleLaplacian x = x := by
  rw [HilbertTransportChain.middleLaplacian]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [splitIncidenceComplex_incomingAdjoint,
    splitIncidenceComplex_outgoingAdjoint]
  apply WithLp.ofLp_injective
  ext <;> simp [splitIncidenceComplex, splitFirstInclusion]

/-- Every middle occurrence is non-harmonic: the two incidence arms span the two summands. -/
theorem splitIncidenceComplex_nonharmonic_eq_top
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    (splitIncidenceComplex V).chain.nonharmonic = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.mem_sup.mpr
  refine ⟨WithLp.toLp 2 (x.fst, 0), ?_, WithLp.toLp 2 (0, x.snd), ?_, ?_⟩
  · exact ⟨x.fst, rfl⟩
  · refine ⟨x.snd, ?_⟩
    exact splitIncidenceComplex_outgoingAdjoint V x.snd
  · apply WithLp.ofLp_injective
    change (x.fst + 0, 0 + x.snd) = (x.fst, x.snd)
    simp

/-- Laplacian energy is squared norm at every scale of the split chain. -/
theorem splitIncidenceComplex_laplacianEnergy_self
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (x : WithLp 2 (V × V)) :
    (splitIncidenceComplex V).chain.laplacianEnergyForm x x = ‖x‖ ^ 2 := by
  rw [HilbertTransportChain.laplacianEnergyForm_apply,
    splitIncidenceComplex_middleLaplacian]
  exact real_inner_self_eq_norm_sq x

/-! ## Refinement along an isometric carrier inclusion -/

/-- A carrier isometry induces a refinement of the complete split incidence chain. -/
def splitIncidenceRefinement
    {V W : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (f : V →ₗᵢ[ℝ] W) :
    HilbertTransportRefinement (splitIncidenceComplex V) (splitIncidenceComplex W) where
  left := f
  middle := f.withLpProdMap 2 f
  right := f
  into_natural := by
    intro x
    apply WithLp.ofLp_injective
    ext <;> simp [splitIncidenceComplex, splitFirstInclusion]
  outOf_natural := by
    intro x
    rfl
  incomingAdjoint_natural := by
    intro x
    rw [splitIncidenceComplex_incomingAdjoint,
      splitIncidenceComplex_incomingAdjoint]
    rfl
  outgoingAdjoint_natural := by
    intro x
    rw [splitIncidenceComplex_outgoingAdjoint,
      splitIncidenceComplex_outgoingAdjoint]
    apply WithLp.ofLp_injective
    change (0, f x) = (f 0, f x)
    simp

/-! ## The unbounded sequential family -/

/-- The carrier at scale `n`; the added `1` keeps both incidence maps nonzero at scale zero. -/
abbrev incidenceCarrier (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- Append one zero coordinate to a Euclidean occurrence. -/
def finSuccLinearMap (n : ℕ) :
    incidenceCarrier n →ₗ[ℝ] incidenceCarrier (n + 1) where
  toFun := fun x ↦ WithLp.toLp 2 (Fin.lastCases 0 x)
  map_add' := by
    intro x y
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  map_smul' := by
    intro c x
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp

@[simp]
theorem finSuccLinearMap_single (n : ℕ) (i : Fin (n + 1)) :
    finSuccLinearMap n (EuclideanSpace.single i 1) =
      EuclideanSpace.single i.castSucc 1 := by
  ext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · have hne : Fin.last (n + 1) ≠ i.castSucc :=
      (Fin.castSucc_ne_last i).symm
    simp [finSuccLinearMap, EuclideanSpace.single_apply, hne]
  · simp [finSuccLinearMap, EuclideanSpace.single_apply,
      Pi.single_apply, Fin.castSucc_inj]

/-- Appending a zero coordinate is a linear isometry. -/
def finSuccInclusion (n : ℕ) :
    incidenceCarrier n →ₗᵢ[ℝ] incidenceCarrier (n + 1) where
  toLinearMap := finSuccLinearMap n
  norm_map' := by
    intro x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_castSucc]
    simp [finSuccLinearMap]

/-- The incidence-bearing object at scale `n`. -/
def incidenceScaleObject (n : ℕ) : FiniteHilbertTransportComplex :=
  splitIncidenceComplex (incidenceCarrier n)

/-- The adjacent scale passage, commuting with both differentials and both adjoints. -/
def incidenceScaleStep (n : ℕ) :
    HilbertTransportRefinement (incidenceScaleObject n) (incidenceScaleObject (n + 1)) :=
  splitIncidenceRefinement (finSuccInclusion n)

/-- Both incidence maps are genuinely nonzero at every scale. -/
theorem incidenceScale_maps_nonzero (n : ℕ) :
    (incidenceScaleObject n).chain.into ≠ 0 ∧
      (incidenceScaleObject n).chain.outOf ≠ 0 := by
  constructor
  · intro h
    have hx := congrArg
      (fun T : (incidenceScaleObject n).Left →L[ℝ]
          (incidenceScaleObject n).Middle ↦
        T (EuclideanSpace.single 0 (1 : ℝ))) h
    change WithLp.toLp 2 (EuclideanSpace.single 0 (1 : ℝ), 0) = 0 at hx
    have hcomponent := congrArg
      (fun z : WithLp 2 (incidenceCarrier n × incidenceCarrier n) ↦ z.fst) hx
    have hzero : EuclideanSpace.single 0 (1 : ℝ) = 0 := by
      simpa using hcomponent
    exact one_ne_zero (EuclideanSpace.single_eq_zero_iff.mp hzero)
  · intro h
    have hx := congrArg
      (fun T : (incidenceScaleObject n).Middle →L[ℝ]
          (incidenceScaleObject n).Right ↦
        T (WithLp.toLp 2 (0, EuclideanSpace.single 0 (1 : ℝ)))) h
    change EuclideanSpace.single 0 (1 : ℝ) = 0 at hx
    exact one_ne_zero (EuclideanSpace.single_eq_zero_iff.mp hx)

/-- The middle carrier has dimension `2(n+1)`. -/
theorem incidenceScale_middle_finrank (n : ℕ) :
    Module.finrank ℝ (incidenceScaleObject n).Middle = 2 * (n + 1) := by
  change Module.finrank ℝ (WithLp 2 (incidenceCarrier n × incidenceCarrier n)) = _
  rw [(WithLp.linearEquiv 2 ℝ
      (incidenceCarrier n × incidenceCarrier n)).finrank_eq,
    Module.finrank_prod]
  simp only [finrank_euclideanSpace_fin]
  omega

/-- The refinement population is unbounded in middle dimension. -/
theorem incidenceScale_middle_finrank_unbounded (N : ℕ) :
    ∃ n : ℕ, N < Module.finrank ℝ (incidenceScaleObject n).Middle := by
  refine ⟨N, ?_⟩
  rw [incidenceScale_middle_finrank]
  omega

/-- Every scale has exactly the same non-harmonic lower bound `1`. -/
theorem incidenceScale_uniformNonharmonicGap :
    ∀ (n : ℕ) (x : (incidenceScaleObject n).chain.nonharmonic),
      (1 : ℝ) * ‖x‖ ^ 2 ≤
        (incidenceScaleObject n).chain.nonharmonicReceiverForm.B x x := by
  intro n x
  rw [one_mul,
    (incidenceScaleObject n).chain.nonharmonicReceiverForm_reading]
  exact (by
    simpa [incidenceScaleObject] using
      (splitIncidenceComplex_laplacianEnergy_self
        (incidenceCarrier n) (x : (incidenceScaleObject n).Middle)).ge)

/-! The exact control returned by this family is therefore positive: unbounded scale and nonzero
incidence alone do not force a gap defect.  A Yang--Mills interpretation still owes the nonlinear
gauge configuration/quotient, interacting Hamiltonian, continuum reconstruction, and physical
dimension hypotheses. -/

section Audit

#print axioms splitIncidenceComplex_middleLaplacian
#print axioms splitIncidenceComplex_nonharmonic_eq_top
#print axioms incidenceScale_maps_nonzero
#print axioms incidenceScale_middle_finrank_unbounded
#print axioms incidenceScale_uniformNonharmonicGap

end Audit

end Soma.Holonics.Millennium.Coupling
