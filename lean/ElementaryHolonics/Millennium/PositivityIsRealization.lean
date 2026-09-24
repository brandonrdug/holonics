import ElementaryHolonics.Millennium.RealizedMillenniumForms
import ElementaryHolonics.Millennium.HelicityAsLinking
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Positivity is realization — the closing theorem of the coupling

`Pivots.theRealizedFormIsDefinite` and its companions transport positivity *backward* along a
realizer: a form that is the pullback of the anchor along an injection is definite.  This file
proves the converse on every finite-dimensional carrier, so the two are one statement:

```
    positive            ⟺  realized:                 ∃ f,  ⟪f x, f y⟫ = B(x, y)
    positive definite   ⟺  realized by an injection
    coercive (a gap)    ⟺  realized by a map bounded below
```

The realizer is the spectral square root: with `b` an orthonormal eigenbasis of the self-adjoint
operator and `λᵢ ≥ 0` its eigenvalues (nonnegative exactly because the form is positive),
`f = b⁻¹ ∘ diag(√λᵢ) ∘ b`.  So on the carriers the Millennium rows live on, **a form is positive
because it is realized, and only then** — positivity is never a property a form has on its own.

Consequences, stated on the instantiated rows: the Stokes dissipation, the transfer coupling for
`|u| ≤ 1`, every Gram of readings, and the rank-12 height form are realized; the helicity form of
the flipped Borromean table and the hyperbolic Hodge-index witness admit **no** realizer at all.
The phase face is not a magnitude, as a theorem.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PositivityIsRealization

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.RealizedMillenniumForms
open Soma.Holonics.Millennium.Pivots
open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A receiver form's operator is symmetric in Mathlib's sense. -/
theorem isSymmetric (G : ReceiverForm V) : (G.T : V →ₗ[ℝ] V).IsSymmetric := by
  intro x y
  exact G.selfAdjoint x y

/-- The eigenvalues of a positive receiver form are nonnegative: `λᵢ = B(bᵢ, bᵢ)`. -/
theorem eigenvalues_nonneg (G : ReceiverForm V) (hpos : G.IsPositive) (i : Fin (Module.finrank ℝ V)) :
    0 ≤ (isSymmetric G).eigenvalues rfl i := by
  set b := (isSymmetric G).eigenvectorBasis rfl
  have hb : G.T (b i) = ((isSymmetric G).eigenvalues rfl i : ℝ) • b i :=
    (isSymmetric G).apply_eigenvectorBasis rfl i
  have hpos_i := hpos (b i)
  rw [ReceiverForm.B] at hpos_i
  change inner ℝ (G.T (b i)) (b i) ≥ 0 at hpos_i
  rw [hb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at hpos_i
  simpa using hpos_i

/-- The reading in eigen-coordinates: `B(x, y) = Σᵢ λᵢ (b x)ᵢ (b y)ᵢ`. -/
theorem reading_eigen (G : ReceiverForm V) (x y : V) :
    G.B x y = ∑ i, (isSymmetric G).eigenvalues rfl i *
      (((isSymmetric G).eigenvectorBasis rfl).repr x i *
        ((isSymmetric G).eigenvectorBasis rfl).repr y i) := by
  set b := (isSymmetric G).eigenvectorBasis rfl with hbdef
  have h : G.B x y = inner ℝ (b.repr (G.T x)) (b.repr y) := by
    rw [ReceiverForm.B, b.repr.inner_map_map]
  rw [h, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hrepr : b.repr (G.T x) i = (isSymmetric G).eigenvalues rfl i * b.repr x i :=
    (isSymmetric G).eigenvectorBasis_apply_self_apply rfl x i
  simp only [RCLike.inner_apply, conj_trivial, hrepr]
  ring

/-- The diagonal scaling by `√λᵢ` in eigen-coordinates. -/
def sqrtScale (G : ReceiverForm V) :
    Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ :=
  fun i j => if i = j then Real.sqrt ((isSymmetric G).eigenvalues rfl i) else 0

/-- [definition] **The spectral realizer** `b⁻¹ ∘ diag(√λᵢ) ∘ b`, as a linear map. -/
def spectralRealizerMap (G : ReceiverForm V) : V →ₗ[ℝ] V where
  toFun x := ((isSymmetric G).eigenvectorBasis rfl).repr.symm
    (matrixMap (sqrtScale G) (((isSymmetric G).eigenvectorBasis rfl).repr x))
  map_add' := by
    intro x y
    simp only [map_add]
  map_smul' := by
    intro c x
    simp only [map_smul, RingHom.id_apply]

/-- The realizer as a continuous linear map. -/
def spectralRealizer (G : ReceiverForm V) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (spectralRealizerMap G)

theorem spectralRealizer_coord (G : ReceiverForm V) (x : V) (i : Fin (Module.finrank ℝ V)) :
    (((isSymmetric G).eigenvectorBasis rfl).repr (spectralRealizer G x)) i =
      Real.sqrt ((isSymmetric G).eigenvalues rfl i) *
        ((isSymmetric G).eigenvectorBasis rfl).repr x i := by
  simp only [spectralRealizer, LinearMap.coe_toContinuousLinearMap', spectralRealizerMap,
    LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.apply_symm_apply, matrixMap_apply,
    sqrtScale]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- [proved-derived; formal-checked] **The spectral realizer realizes a positive form.** -/
theorem spectralRealizer_preserves (G : ReceiverForm V) (hpos : G.IsPositive) (x y : V) :
    inner ℝ (spectralRealizer G x) (spectralRealizer G y) = G.B x y := by
  set b := (isSymmetric G).eigenvectorBasis rfl with hbdef
  rw [← b.repr.inner_map_map, PiLp.inner_apply, reading_eigen]
  apply Finset.sum_congr rfl
  intro i _
  have hx := spectralRealizer_coord G x i
  have hy := spectralRealizer_coord G y i
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy]
  have hsq := Real.mul_self_sqrt (eigenvalues_nonneg G hpos i)
  linear_combination (b.repr x i * b.repr y i) * hsq

/-! ## The closing equivalences -/

/-- [proved-derived; formal-checked] **Positivity is realization**: a receiver form on a
finite-dimensional carrier is positive exactly when it is the pullback of the anchor along some
map. -/
theorem positive_iff_realized (G : ReceiverForm V) :
    G.IsPositive ↔ ∃ f : V →L[ℝ] V, ∀ x y, inner ℝ (f x) (f y) = G.B x y := by
  constructor
  · intro hpos
    exact ⟨spectralRealizer G, spectralRealizer_preserves G hpos⟩
  · rintro ⟨f, hf⟩
    exact theRealizedFormIsPositive G f hf

/-- [proved-derived; formal-checked] **Positive definite is realization by an injection.** -/
theorem positiveDefinite_iff_realized_injective (G : ReceiverForm V) :
    (G.IsPositive ∧ G.IsDefinite) ↔
      ∃ f : V →L[ℝ] V, (∀ x y, inner ℝ (f x) (f y) = G.B x y) ∧ ∀ x, f x = 0 → x = 0 := by
  constructor
  · rintro ⟨hpos, hdef⟩
    refine ⟨spectralRealizer G, spectralRealizer_preserves G hpos, ?_⟩
    intro x hx
    apply hdef
    rw [← spectralRealizer_preserves G hpos x x, hx]
    simp
  · rintro ⟨f, hf, hinj⟩
    exact ⟨theRealizedFormIsPositive G f hf, theRealizedFormIsDefinite G f hf hinj⟩

/-- [proved-derived; formal-checked] **A gap is realization by a map bounded below.** -/
theorem coercive_iff_realized_boundedBelow (G : ReceiverForm V) :
    G.IsCoercive ↔
      ∃ (f : V →L[ℝ] V) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ≤ ‖f x‖) ∧
        ∀ x y, inner ℝ (f x) (f y) = G.B x y := by
  constructor
  · intro hcoer
    obtain ⟨Δ, hΔ, hB⟩ := hcoer
    have hpos : G.IsPositive := G.theGapForcesPositivity ⟨Δ, hΔ, hB⟩
    refine ⟨spectralRealizer G, Real.sqrt Δ, Real.sqrt_pos.mpr hΔ, ?_,
      spectralRealizer_preserves G hpos⟩
    intro x
    have hnorm : ‖spectralRealizer G x‖ ^ 2 = G.B x x := by
      rw [← real_inner_self_eq_norm_sq, spectralRealizer_preserves G hpos]
    have h1 : (Real.sqrt Δ * ‖x‖) ^ 2 ≤ ‖spectralRealizer G x‖ ^ 2 := by
      rw [hnorm, mul_pow, Real.sq_sqrt (le_of_lt hΔ)]
      exact hB x
    have ha : 0 ≤ Real.sqrt Δ * ‖x‖ := by positivity
    have hb : 0 ≤ ‖spectralRealizer G x‖ := norm_nonneg _
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at h2
  · rintro ⟨f, c, hc, hbelow, hf⟩
    exact theRealizationBoundedBelowGivesTheGap G f hc hbelow hf

/-! ## The rows, as corollaries -/

open Soma.Holonics.Millennium.HelicityAsLinking
open Soma.Holonics.Millennium.Crossings

/-- Every Gram of readings is realized (positive by `gramForm_positive`). -/
theorem gramForm_realized {n m : ℕ} (w : Fin n → Carrier m) :
    ∃ f : Carrier n →L[ℝ] Carrier n, ∀ x y, inner ℝ (f x) (f y) = (gramForm w).B x y :=
  (positive_iff_realized _).mp (gramForm_positive w)

/-- The Stokes dissipation is realized with a gap. -/
theorem stokesForm_realized {n : ℕ} (k : Fin n → ℝ) (hk : ∀ i, 1 ≤ k i ^ 2) :
    ∃ (f : Carrier n →L[ℝ] Carrier n) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ≤ ‖f x‖) ∧
      ∀ x y, inner ℝ (f x) (f y) = (stokesForm k).B x y :=
  (coercive_iff_realized_boundedBelow _).mp (stokesForm_coercive k hk)

/-- The transfer coupling is realized with a gap for `|u| < 1`. -/
theorem transferForm_realized (u : ℝ) (hu : |u| < 1) :
    ∃ (f : Carrier 2 →L[ℝ] Carrier 2) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ≤ ‖f x‖) ∧
      ∀ x y, inner ℝ (f x) (f y) = (transferForm u).B x y :=
  (coercive_iff_realized_boundedBelow _).mp (transferForm_coercive u hu)

/-- The rank-12 height form is realized by an injection. -/
theorem mestreForm_realized :
    ∃ f : Carrier 12 →L[ℝ] Carrier 12,
      (∀ x y, inner ℝ (f x) (f y) = mestreForm.B x y) ∧ ∀ x, f x = 0 → x = 0 :=
  (positiveDefinite_iff_realized_injective _).mp ⟨mestreForm_positive, mestreForm_definite⟩

/-- [proved-derived; formal-checked] **The phase face is not a magnitude**: the helicity form of
the flipped Borromean table admits no realizer. -/
theorem helicityForm_not_realized :
    ¬ ∃ f : Carrier 3 →L[ℝ] Carrier 3,
      ∀ x y, inner ℝ (f x) (f y) = (helicityForm borromeanSameHandVariant).B x y := by
  rw [← positive_iff_realized]
  exact helicityForm_not_positive

/-- The Hodge-index witness of signature `(1, 1)` admits no realizer. -/
theorem hyperbolicForm_not_realized :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      ∀ x y, inner ℝ (f x) (f y) = hyperbolicForm.B x y := by
  rw [← positive_iff_realized]
  exact theHyperbolicFormIsNotPositive

section Audit

#print axioms spectralRealizer_preserves
#print axioms positive_iff_realized
#print axioms positiveDefinite_iff_realized_injective
#print axioms coercive_iff_realized_boundedBelow
#print axioms helicityForm_not_realized
#print axioms hyperbolicForm_not_realized

end Audit

end Soma.Holonics.Millennium.PositivityIsRealization
