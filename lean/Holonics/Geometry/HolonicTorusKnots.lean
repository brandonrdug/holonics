import Mathlib.Topology.Instances.AddCircle.Real
import Holonics.Transport.HolonicComposition
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Path
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Oriented torus paths and coprime slope embeddings

An integral pair first constructs a continuous oriented loop on the genuine geometric two-torus.
Its canonical real lift starts at zero and returns with exactly that integral displacement; this is
the winding receiver.  The same pair defines a circle map into the torus.  Bézout's identity proves
that a coprime pair makes this map injective, and compact-to-Hausdorff topology upgrades it to an
embedding.  Thus the `(p,q)` torus knot is constructed as an embedded geometric circle in `T^2`,
not as a crossing table.  A primitive integral slope, of either sign, is already an injective
circle map (`torusSlopeMap_injective_of_isCoprime`).

Two primitive, nonparallel straight circles cross in exactly `|det|` points at every offset
(`torus_geodesic_crossings`): their crossings are a coset set of the lattice their slopes span
(`crossingSetEquiv`), whose index is the determinant (`slopeLattice_index`).

The traversible-band connection is made at the exact statement its evidence supports: an odd
`m`-half-twist boundary has the coprime slope `(2,m)`.  No isotopy or Euclidean torus-surface theorem
is inferred from the engine's classification enum.
-/

noncomputable section

namespace Holonics.Geometry.HolonicTorusKnots

open Holonics
open Topology unitInterval

/-- The genuine geometric two-torus. -/
abbrev GeometricTwoTorus := UnitAddTorus (Fin 2)

/-- The coordinatewise quotient projection from the canonical real covering chart. -/
def realToTwoTorus (x : Fin 2 → ℝ) : GeometricTwoTorus :=
  fun i => (x i : UnitAddCircle)

/-- The canonical straight lift of an integral slope. -/
def torusSlopeLift (winding : Fin 2 → ℤ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => (winding i : ℝ) * t

/-- The intrinsic circle map of the same integral slope. -/
def torusSlopeMap (winding : Fin 2 → ℤ) : C(UnitAddCircle, GeometricTwoTorus) where
  toFun phase i := winding i • phase
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro i
    exact continuous_zsmul (winding i)

@[simp]
theorem torusSlopeMap_apply (winding : Fin 2 → ℤ) (phase : UnitAddCircle) (i : Fin 2) :
    torusSlopeMap winding phase i = winding i • phase := rfl

/-- Projecting the straight lift returns the intrinsic torus circle at every real time. -/
theorem realToTwoTorus_torusSlopeLift (winding : Fin 2 → ℤ) (t : ℝ) :
    realToTwoTorus (torusSlopeLift winding t) =
      torusSlopeMap winding (t : UnitAddCircle) := by
  ext i
  change (((winding i : ℝ) * t : ℝ) : UnitAddCircle) =
    winding i • (t : UnitAddCircle)
  rw [← QuotientAddGroup.mk_zsmul]
  simp only [zsmul_eq_mul]

@[simp]
theorem torusSlopeLift_zero (winding : Fin 2 → ℤ) :
    torusSlopeLift winding 0 = 0 := by
  ext i
  simp [torusSlopeLift]

/-- The lift's endpoint displacement is the integral winding pair in the real chart. -/
theorem torusSlopeLift_endpoint_displacement (winding : Fin 2 → ℤ) (i : Fin 2) :
    torusSlopeLift winding 1 i - torusSlopeLift winding 0 i = winding i := by
  simp [torusSlopeLift]

/-- The integral slope gives a genuinely closed oriented path on the geometric two-torus. -/
def torusSlopePath (winding : Fin 2 → ℤ) :
    Path (0 : GeometricTwoTorus) 0 where
  toContinuousMap :=
    { toFun := fun t => torusSlopeMap winding ((t : ℝ) : UnitAddCircle)
      continuous_toFun :=
        (torusSlopeMap winding).continuous.comp
          (QuotientAddGroup.continuous_mk.comp continuous_subtype_val) }
  source' := by
    ext i
    simp [torusSlopeMap]
  target' := by
    ext i
    simp [torusSlopeMap, ← QuotientAddGroup.mk_zsmul]

/-- The path is carried as an addressed geometric occurrence before its winding is re-read. -/
def torusSlopePathPassage :
    AddressedPassage (Fin 2 → ℤ) (Path (0 : GeometricTwoTorus) 0) :=
  AddressedPassage.graph torusSlopePath

theorem torusSlopePathPassage_retains_winding (winding : Fin 2 → ℤ) :
    Nonempty ((torusSlopePathPassage).Fibre winding (torusSlopePath winding)) :=
  ⟨AddressedPassage.graphFibre _ winding⟩

/-! ## Coprime slopes embed one geometric circle -/

/-- Bézout combines the two coordinate equalities into equality of the source phases: a primitive
integral slope is an injective circle map. -/
theorem torusSlopeMap_injective_of_isCoprime (winding : Fin 2 → ℤ)
    (hprim : IsCoprime (winding 0) (winding 1)) :
    Function.Injective (torusSlopeMap winding) := by
  intro x y hxy
  obtain ⟨α, β, hbezout⟩ := hprim
  let d : UnitAddCircle := x - y
  have hd0 : winding 0 • d = 0 := by
    dsimp [d]
    rw [zsmul_sub, show winding 0 • x = winding 0 • y from congrFun hxy 0, sub_self]
  have hd1 : winding 1 • d = 0 := by
    dsimp [d]
    rw [zsmul_sub, show winding 1 • x = winding 1 • y from congrFun hxy 1, sub_self]
  have hd : d = 0 := by
    calc
      d = (1 : ℤ) • d := (one_zsmul _).symm
      _ = (α * winding 0 + β * winding 1) • d := by rw [hbezout]
      _ = α • (winding 0 • d) + β • (winding 1 • d) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hd0, hd1]; simp
  exact sub_eq_zero.mp hd

/-- The natural coprime case. -/
theorem torusSlopeMap_injective_of_coprime (p q : ℕ) (hpq : Nat.Coprime p q) :
    Function.Injective (torusSlopeMap ![(p : ℤ), (q : ℤ)]) :=
  torusSlopeMap_injective_of_isCoprime _ (by simpa using Nat.isCoprime_iff_coprime.mpr hpq)

/-- A coprime slope is a closed embedding of a circle in the genuine geometric torus. -/
theorem torusSlopeMap_isEmbedding_of_coprime (p q : ℕ) (hpq : Nat.Coprime p q) :
    IsEmbedding (torusSlopeMap ![(p : ℤ), (q : ℤ)]) :=
  ((torusSlopeMap ![(p : ℤ), (q : ℤ)]).continuous.isClosedEmbedding
    (torusSlopeMap_injective_of_coprime p q hpq)).isEmbedding

/-- The geometric `(p,q)` torus knot is the embedded image of its coprime slope circle. -/
def torusKnotSet (p q : ℕ) : Set GeometricTwoTorus :=
  Set.range (torusSlopeMap ![(p : ℤ), (q : ℤ)])

theorem torusKnotSet_isCompact (p q : ℕ) : IsCompact (torusKnotSet p q) := by
  exact isCompact_range (torusSlopeMap ![(p : ℤ), (q : ℤ)]).continuous

/-! ## The traversible half-twist reading returns the slope `(2,m)` -/

/-- Odd half-twist count is exactly the coprimality needed by the `(2,m)` boundary slope. -/
theorem oddHalfTwist_boundarySlope_coprime (m : ℕ) (hm : Odd m) : Nat.Coprime 2 m :=
  Nat.coprime_two_left.mpr hm

/-- Therefore every odd traversible-band count constructs an embedded `(2,m)` boundary circle. -/
theorem oddHalfTwist_boundary_isTorusKnotEmbedding (m : ℕ) (hm : Odd m) :
    IsEmbedding (torusSlopeMap ![(2 : ℤ), (m : ℤ)]) :=
  torusSlopeMap_isEmbedding_of_coprime 2 m (oddHalfTwist_boundarySlope_coprime m hm)

/-- The constructed boundary's canonical lift returns exactly the asserted `(2,m)` slope. -/
theorem oddHalfTwist_boundary_lift_returns_slope (m : ℕ) (i : Fin 2) :
    torusSlopeLift ![(2 : ℤ), (m : ℤ)] 1 i -
      torusSlopeLift ![(2 : ℤ), (m : ℤ)] 0 i = ![(2 : ℤ), (m : ℤ)] i :=
  torusSlopeLift_endpoint_displacement _ i

/-! ## Two straight torus circles cross in `|det|` points

[proved-derived; formal-checked] Two closed torus circles of primitive integral slopes `w₁ = (a, b)`
and `w₂ = (c, d)`, the second translated by any offset `u`, cross where
`s w₁ − t w₂ ≡ u (mod ℤ²)`: a `2 × 2` integer system. Its solutions, modulo the periods of both
circles, are a coset set of the slope lattice `M ℤ²`, `M = [[a, c], [b, d]]`
(`crossingSetEquiv`), whose index is `|det M| = |ad − bc|` (`slopeLattice_index`, through Mathlib's
Smith normal form count `Submodule.natAbs_det_equiv`). So the circles cross in exactly `|ad − bc|`
points at every offset (`torus_geodesic_crossings`): the moiré's cells are the determinant, the
area of the parallelogram the two windings span. -/

/-- [definition] The determinant of two integral slopes. -/
def slopeDet (w₁ w₂ : Fin 2 → ℤ) : ℤ := w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0

/-- [definition] The integral matrix whose columns are the two slopes. -/
def slopeMatrix (w₁ w₂ : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![w₁ 0, w₂ 0; w₁ 1, w₂ 1]

theorem slopeMatrix_det (w₁ w₂ : Fin 2 → ℤ) : (slopeMatrix w₁ w₂).det = slopeDet w₁ w₂ := by
  simp [slopeMatrix, slopeDet, Matrix.det_fin_two]
  ring

/-- [definition] The lattice the two slopes span, `M ℤ²`. -/
abbrev slopeLattice (w₁ w₂ : Fin 2 → ℤ) : Submodule ℤ (Fin 2 → ℤ) :=
  LinearMap.range (Matrix.toLin' (slopeMatrix w₁ w₂))

/-- [proved-derived; formal-checked] **The index of the slope lattice is `|det|`.** -/
theorem slopeLattice_index (w₁ w₂ : Fin 2 → ℤ) (hdet : slopeDet w₁ w₂ ≠ 0) :
    Nat.card ((Fin 2 → ℤ) ⧸ slopeLattice w₁ w₂) = (slopeDet w₁ w₂).natAbs := by
  have hf : Function.Injective (Matrix.toLin' (slopeMatrix w₁ w₂)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    apply hdet
    rw [← slopeMatrix_det]
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hne, by simpa using hv⟩
  let e := LinearEquiv.ofInjective (Matrix.toLin' (slopeMatrix w₁ w₂)) hf
  rw [← Submodule.natAbs_det_equiv (slopeLattice w₁ w₂) e]
  have hcomp : (slopeLattice w₁ w₂).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap (e : (Fin 2 → ℤ) →+ slopeLattice w₁ w₂) =
        Matrix.toLin' (slopeMatrix w₁ w₂) := by
    refine LinearMap.ext fun x => ?_
    simp [e]
  rw [hcomp, LinearMap.det_toLin', slopeMatrix_det]

/-- [definition] **The crossing set** of the slope-`w₁` circle and the slope-`w₂` circle
translated by the offset `u`. -/
def crossingSet (w₁ w₂ : Fin 2 → ℤ) (u : Fin 2 → ℝ) : Set GeometricTwoTorus :=
  Set.range (torusSlopeMap w₁) ∩
    {z | ∃ t : UnitAddCircle, z = torusSlopeMap w₂ t + realToTwoTorus u}

theorem zsmul_coe_unitAddCircle (w : ℤ) (x : ℝ) :
    w • (x : UnitAddCircle) = ((w * x : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem coe_eq_coe_iff_int (a b : ℝ) :
    (a : UnitAddCircle) = b ↔ ∃ n : ℤ, a - b = n := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩

/-- [definition] The first circle's crossing phase at the integer class `n` (Cramer's rule for
`s w₁ − t w₂ = n + u`). -/
noncomputable def crossingPhase (w₁ w₂ : Fin 2 → ℤ) (u : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ℝ :=
  ((w₂ 1 : ℝ) * (n 0 + u 0) - (w₂ 0 : ℝ) * (n 1 + u 1)) / slopeDet w₁ w₂

/-- [definition] The second circle's crossing phase at the integer class `n`. -/
noncomputable def crossingPhase₂ (w₁ w₂ : Fin 2 → ℤ) (u : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ℝ :=
  ((w₁ 1 : ℝ) * (n 0 + u 0) - (w₁ 0 : ℝ) * (n 1 + u 1)) / slopeDet w₁ w₂

theorem crossingPhase_solves {w₁ w₂ : Fin 2 → ℤ} (hdet : slopeDet w₁ w₂ ≠ 0) (u : Fin 2 → ℝ)
    (n : Fin 2 → ℤ) (i : Fin 2) :
    (w₁ i : ℝ) * crossingPhase w₁ w₂ u n - (w₂ i : ℝ) * crossingPhase₂ w₁ w₂ u n = n i + u i := by
  have hD : ((slopeDet w₁ w₂ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
  unfold crossingPhase crossingPhase₂
  rw [← mul_div_assoc, ← mul_div_assoc, div_sub_div_same, div_eq_iff hD]
  simp only [slopeDet]
  push_cast
  fin_cases i <;> simp <;> ring

/-- [definition] **The crossing point** of the integer class `n`. -/
noncomputable def crossingPoint (w₁ w₂ : Fin 2 → ℤ) (u : Fin 2 → ℝ) (n : Fin 2 → ℤ) :
    GeometricTwoTorus :=
  torusSlopeMap w₁ (crossingPhase w₁ w₂ u n : UnitAddCircle)

theorem crossingPoint_eq_second {w₁ w₂ : Fin 2 → ℤ} (hdet : slopeDet w₁ w₂ ≠ 0)
    (u : Fin 2 → ℝ) (n : Fin 2 → ℤ) :
    crossingPoint w₁ w₂ u n =
      torusSlopeMap w₂ (crossingPhase₂ w₁ w₂ u n : UnitAddCircle) + realToTwoTorus u := by
  funext i
  simp only [crossingPoint, torusSlopeMap_apply, Pi.add_apply, realToTwoTorus,
    zsmul_coe_unitAddCircle, ← AddCircle.coe_add, coe_eq_coe_iff_int]
  exact ⟨n i, by linear_combination crossingPhase_solves hdet u n i⟩

theorem crossingPoint_mem {w₁ w₂ : Fin 2 → ℤ} (hdet : slopeDet w₁ w₂ ≠ 0) (u : Fin 2 → ℝ)
    (n : Fin 2 → ℤ) : crossingPoint w₁ w₂ u n ∈ crossingSet w₁ w₂ u :=
  ⟨⟨_, rfl⟩, ⟨_, crossingPoint_eq_second hdet u n⟩⟩

/-- [proved-derived; formal-checked] **Two integer classes give one crossing exactly when they
differ by the slope lattice.** -/
theorem crossingPoint_eq_iff {w₁ w₂ : Fin 2 → ℤ} (h₁ : IsCoprime (w₁ 0) (w₁ 1))
    (h₂ : IsCoprime (w₂ 0) (w₂ 1)) (hdet : slopeDet w₁ w₂ ≠ 0) (u : Fin 2 → ℝ)
    (n n' : Fin 2 → ℤ) :
    crossingPoint w₁ w₂ u n = crossingPoint w₁ w₂ u n' ↔ n - n' ∈ slopeLattice w₁ w₂ := by
  have hD : ((slopeDet w₁ w₂ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
  constructor
  · intro h
    have hs := torusSlopeMap_injective_of_isCoprime w₁ h₁ h
    have ht : (crossingPhase₂ w₁ w₂ u n : UnitAddCircle) = crossingPhase₂ w₁ w₂ u n' := by
      have e := (crossingPoint_eq_second hdet u n).symm.trans
        (h.trans (crossingPoint_eq_second hdet u n'))
      exact torusSlopeMap_injective_of_isCoprime w₂ h₂ (add_right_cancel e)
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int _ _).mp hs
    obtain ⟨l, hl⟩ := (coe_eq_coe_iff_int _ _).mp ht
    have hint : ∀ i, w₁ i * k - w₂ i * l = n i - n' i := fun i => by
      have hreal : ((w₁ i * k - w₂ i * l : ℤ) : ℝ) = ((n i - n' i : ℤ) : ℝ) := by
        push_cast
        linear_combination crossingPhase_solves hdet u n i - crossingPhase_solves hdet u n' i -
          (w₁ i : ℝ) * hk + (w₂ i : ℝ) * hl
      exact_mod_cast hreal
    refine ⟨![k, -l], funext fun i => ?_⟩
    have := hint i
    fin_cases i <;>
      simp [Matrix.toLin'_apply, slopeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
      linarith
  · rintro ⟨v, hv⟩
    have hint : ∀ i, w₁ i * v 0 + w₂ i * v 1 = n i - n' i := fun i => by
      have := congrFun hv i
      fin_cases i <;>
        simp [Matrix.toLin'_apply, slopeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
        linarith
    have h0 : ((w₁ 0 * v 0 + w₂ 0 * v 1 : ℤ) : ℝ) = ((n 0 - n' 0 : ℤ) : ℝ) := by
      exact_mod_cast hint 0
    have h1 : ((w₁ 1 * v 0 + w₂ 1 * v 1 : ℤ) : ℝ) = ((n 1 - n' 1 : ℤ) : ℝ) := by
      exact_mod_cast hint 1
    push_cast at h0 h1
    unfold crossingPoint
    congr 1
    rw [coe_eq_coe_iff_int]
    refine ⟨v 0, ?_⟩
    unfold crossingPhase
    rw [div_sub_div_same, div_eq_iff hD]
    simp only [slopeDet]
    push_cast
    linear_combination (-(w₂ 1 : ℝ)) * h0 + (w₂ 0 : ℝ) * h1

/-- [proved-derived; formal-checked] Every crossing is the crossing point of an integer class. -/
theorem crossingPoint_surjective {w₁ w₂ : Fin 2 → ℤ} (hdet : slopeDet w₁ w₂ ≠ 0)
    (u : Fin 2 → ℝ) {z : GeometricTwoTorus} (hz : z ∈ crossingSet w₁ w₂ u) :
    ∃ n, crossingPoint w₁ w₂ u n = z := by
  have hD : ((slopeDet w₁ w₂ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
  obtain ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩ := hz
  obtain ⟨s₀, rfl⟩ := QuotientAddGroup.mk_surjective s
  obtain ⟨t₀, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hi : ∀ i, ∃ m : ℤ, (w₁ i : ℝ) * s₀ - ((w₂ i : ℝ) * t₀ + u i) = m := fun i => by
    have := congrFun ht i
    simp only [torusSlopeMap_apply, Pi.add_apply, realToTwoTorus] at this
    change w₁ i • ((s₀ : ℝ) : UnitAddCircle) = w₂ i • ((t₀ : ℝ) : UnitAddCircle) + _ at this
    rw [zsmul_coe_unitAddCircle, zsmul_coe_unitAddCircle, ← AddCircle.coe_add,
      coe_eq_coe_iff_int] at this
    exact this
  choose n hn using hi
  refine ⟨n, ?_⟩
  unfold crossingPoint
  congr 2
  unfold crossingPhase
  rw [div_eq_iff hD]
  simp only [slopeDet]
  push_cast
  linear_combination (-(w₂ 1 : ℝ)) * hn 0 + (w₂ 0 : ℝ) * hn 1

/-- [proved-derived; formal-checked] **The crossings are a coset set of the slope lattice.** -/
noncomputable def crossingSetEquiv {w₁ w₂ : Fin 2 → ℤ} (h₁ : IsCoprime (w₁ 0) (w₁ 1))
    (h₂ : IsCoprime (w₂ 0) (w₂ 1)) (hdet : slopeDet w₁ w₂ ≠ 0) (u : Fin 2 → ℝ) :
    crossingSet w₁ w₂ u ≃ (Fin 2 → ℤ) ⧸ slopeLattice w₁ w₂ :=
  let f : (Fin 2 → ℤ) → crossingSet w₁ w₂ u :=
    fun n => ⟨crossingPoint w₁ w₂ u n, crossingPoint_mem hdet u n⟩
  have hf : Function.Surjective f := fun z => by
    obtain ⟨n, hn⟩ := crossingPoint_surjective hdet u z.2
    exact ⟨n, Subtype.ext hn⟩
  (Setoid.quotientKerEquivOfSurjective f hf).symm.trans
    (Quotient.congrRight fun n n' => by
      rw [Setoid.ker_def, Submodule.quotientRel_def]
      exact Subtype.ext_iff.trans (crossingPoint_eq_iff h₁ h₂ hdet u n n'))

/-- [proved-derived; formal-checked] **`torus_geodesic_crossings`.** Two torus circles of primitive,
nonparallel integral slopes `(a, b)` and `(c, d)` cross in exactly `|ad − bc|` points, at every
offset. -/
theorem torus_geodesic_crossings {w₁ w₂ : Fin 2 → ℤ} (h₁ : IsCoprime (w₁ 0) (w₁ 1))
    (h₂ : IsCoprime (w₂ 0) (w₂ 1)) (hdet : slopeDet w₁ w₂ ≠ 0) (u : Fin 2 → ℝ) :
    Nat.card (crossingSet w₁ w₂ u) = (slopeDet w₁ w₂).natAbs := by
  rw [Nat.card_congr (crossingSetEquiv h₁ h₂ hdet u), slopeLattice_index w₁ w₂ hdet]

/-! ## A finite torus probe does not determine integral winding -/

def slopeModuloFour (winding : Fin 2 → ℤ) : Fin 2 → ZMod 4 :=
  fun i => winding i

/-- Integral slopes `0` and `4` agree at the finite phase probe but are not the same winding. -/
theorem finiteModuloFourProbe_does_not_identify_integralSlope :
    slopeModuloFour ![(0 : ℤ), (0 : ℤ)] = slopeModuloFour ![(4 : ℤ), (0 : ℤ)] ∧
      ![(0 : ℤ), (0 : ℤ)] ≠ ![(4 : ℤ), (0 : ℤ)] := by
  constructor
  · funext i
    fin_cases i <;> decide
  · decide

end Holonics.Geometry.HolonicTorusKnots

section Audit
open Holonics.Geometry.HolonicTorusKnots
#print axioms realToTwoTorus_torusSlopeLift
#print axioms torusSlopeLift_endpoint_displacement
#print axioms torusSlopePathPassage_retains_winding
#print axioms torusSlopeMap_injective_of_isCoprime
#print axioms torusSlopeMap_injective_of_coprime
#print axioms slopeLattice_index
#print axioms crossingPoint_eq_iff
#print axioms torus_geodesic_crossings
#print axioms torusSlopeMap_isEmbedding_of_coprime
#print axioms torusKnotSet_isCompact
#print axioms oddHalfTwist_boundary_isTorusKnotEmbedding
#print axioms oddHalfTwist_boundary_lift_returns_slope
#print axioms finiteModuloFourProbe_does_not_identify_integralSlope
end Audit
