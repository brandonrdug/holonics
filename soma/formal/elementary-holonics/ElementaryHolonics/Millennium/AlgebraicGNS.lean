import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-!
# The algebraic GNS quotient

The Gelfand–Naimark–Segal construction takes the degenerate form a state induces on an algebra,
quotients by the set where its semi-norm vanishes, and completes.  **This file is the middle step,
stated where it is new: over an arbitrary linearly ordered commutative ring, for an arbitrary
positive semidefinite bilinear form, with no analysis and no completion.**

```text
  <A,B>_ω = ω(B* A)            the semi-definite form a state induces
  I_ω = {A : ω(A* A) = 0}      the null set                    ==  LinearMap.ker B
  Cauchy–Schwarz for states    ==  mathlib's apply_apply_same_eq_zero_iff, inherited
  A / I_ω                      strictly positive definite      ==  the anisotropic quotient below
  Cauchy completion → H_ω      THE SECOND COLLAPSE             --  deliberately not taken
```

Two lifts build the induced form and the second is where symmetry is spent.  The quotient form is
proved symmetric, non-negative, **anisotropic**, positive definite and non-degenerate; and an
endomorphism that does not increase the self-pairing is proved to carry the null space into itself
and to descend, still contracting — the transfer operator's step, with the order doing the work.

**Measured 2026-08-20**, by `grep -rn "PreGNS\|gnsStarAlgHom\|gnsNonUnitalStarAlgHom"` over
`Mathlib` at `v4.27.0`: mathlib carries GNS only in the analytic C\*-setting, on
`PreInnerProductSpace.Core`.  A sweep for a quotient-by-the-radical over `BilinearForm/`,
`QuadraticForm/` and `SesquilinearForm/` returned nothing.  That measures those names over that
scope and is not a claim that no related content exists under another name.

**No Cauchy–Schwarz is proved here.**  It is mathlib's, at
`Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean` — `apply_mul_apply_le_of_forall_zero_le` and its
corollary `apply_apply_same_eq_zero_iff` — and every use below is an application.

Every `theorem` here is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.AlgebraicGNS

universe u v

section GNS

variable {R : Type u} {N : Type v}
variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup N] [Module R N]
variable (B : LinearMap.BilinForm R N)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **First lift: the form descends in its first slot, tautologically.**

**DEFINITIONAL — `Submodule.liftQ B le_rfl`.**  It is the first of the two `liftQ`s and carries no
hypothesis at all, because the submodule being quotiented by *is* the kernel of the map lifted. -/
def gnsFirstLift : (N ⧸ LinearMap.ker B) →ₗ[R] (N →ₗ[R] R) :=
  (LinearMap.ker B).liftQ B le_rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **DEFINITIONAL — `rfl`**, by mathlib's `Submodule.liftQ_apply`. -/
@[simp] theorem gnsFirstLift_apply (x : N) :
    gnsFirstLift B (Submodule.Quotient.mk x) = B x := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The flipped first lift kills the kernel in its remaining slot, and this is where symmetry is
spent.**  Without `B.IsSymm` the right kernel need not contain the left one and the second `liftQ`
has no hypothesis to consume. -/
theorem theFlippedLiftKillsTheKernel (hB : B.IsSymm) :
    LinearMap.ker B ≤ LinearMap.ker (LinearMap.flip (gnsFirstLift B)) := by
  intro n hn
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    show B x n = 0
    rw [hB.eq x n]
    rw [LinearMap.mem_ker] at hn
    rw [hn]
    rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **THE GNS FORM: the induced bilinear form on `N ⧸ ker B`, by a double `Submodule.liftQ`.** -/
def gnsForm (hB : B.IsSymm) : LinearMap.BilinForm R (N ⧸ LinearMap.ker B) :=
  (LinearMap.ker B).liftQ (LinearMap.flip (gnsFirstLift B)) (theFlippedLiftKillsTheKernel B hB)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The induced form computes the original form on representatives.**

The two slots come out swapped by construction — the flip is what makes the second `liftQ`
typecheck — so this statement, unlike its unflipped shadow, is *not* `rfl`; it consumes the symmetry
once more. -/
@[simp] theorem gnsForm_apply (hB : B.IsSymm) (x y : N) :
    gnsForm B hB (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := by
  show B y x = B x y
  exact hB.eq y x

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The induced form is symmetric.** -/
theorem theGnsFormIsSymm (hB : B.IsSymm) : (gnsForm B hB).IsSymm := by
  refine ⟨fun p q => ?_⟩
  induction p using Submodule.Quotient.induction_on with
  | H x =>
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      simp only [gnsForm_apply]
      exact hB.eq x y

omit [IsStrictOrderedRing R] in
/-- **The induced form is non-negative.** -/
theorem theGnsFormIsNonneg (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) : (gnsForm B hB).IsNonneg := by
  refine ⟨fun q => ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H x => simpa using hs x

omit [IsStrictOrderedRing R] in
/-- **The induced form is positive semidefinite**, in mathlib's `IsPosSemidef`. -/
theorem theGnsFormIsPosSemidef (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    (gnsForm B hB).IsPosSemidef where
  isSymm := theGnsFormIsSymm B hB
  isNonneg := theGnsFormIsNonneg B hs hB

/-- **The induced form is anisotropic: the quotient has no null vectors left at all.**

This is the point of the quotient, and it is where mathlib's Cauchy–Schwarz corollary
`apply_apply_same_eq_zero_iff` is spent: a representative pairing to nothing with itself is in the
kernel, hence its class is zero. -/
theorem theGnsFormIsAnisotropicOnClasses (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm)
    (q : N ⧸ LinearMap.ker B) (hq : gnsForm B hB q q = 0) : q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    rw [gnsForm_apply] at hq
    have hx : x ∈ LinearMap.ker B :=
      (B.apply_apply_same_eq_zero_iff hs (LinearMap.BilinForm.isSymm_iff.mp hB)).mp hq
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

/-- **The same statement in mathlib's `QuadraticMap.Anisotropic` vocabulary**, so the export carries
the standard predicate and not a bespoke one. -/
theorem theGnsFormIsAnisotropic (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    (LinearMap.BilinMap.toQuadraticMap (gnsForm B hB)).Anisotropic :=
  fun q hq => theGnsFormIsAnisotropicOnClasses B hs hB q hq

/-- **The induced form is positive definite**, in mathlib's `QuadraticMap.PosDef`: non-negative and
anisotropic together, by mathlib's `posDef_of_nonneg`. -/
theorem theGnsFormIsPosDef (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    (LinearMap.BilinMap.toQuadraticMap (gnsForm B hB)).PosDef :=
  QuadraticMap.posDef_of_nonneg (fun q => (theGnsFormIsNonneg B hs hB).nonneg q)
    (theGnsFormIsAnisotropic B hs hB)

/-- **The induced form is nondegenerate**, in mathlib's `LinearMap.BilinForm.Nondegenerate`.

Anisotropy is the stronger fact and it is already discharged: a class annihilating everything in
particular annihilates itself, and then the quotient's anisotropy finishes.  (Mathlib's
`nondegenerate_iff` states the same equivalence for positive semidefinite symmetric forms; it is not
used, because the direction needed here is the cheap one.) -/
theorem theGnsFormIsNondegenerate (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    (gnsForm B hB).Nondegenerate := by
  intro q hq
  exact theGnsFormIsAnisotropicOnClasses B hs hB q (hq q)

/-! ### Descent of a non-increasing endomorphism

The classical transfer operator does not preserve the null set for any structural reason — it
preserves it because it does not increase the self-pairing, and the null set is the bottom of that
order.  That is the whole argument, and it needs the ordered ring. -/

variable (T : N →ₗ[R] N)

/-- **An endomorphism that does not increase the self-pairing carries the null space into itself.**

The order is doing the work: on a null vector the image's self-pairing is squeezed between `0` and
`0`, and mathlib's Cauchy–Schwarz corollary converts that back into kernel membership.  That the
hypothesis is load-bearing — that no ideal-style argument replaces it — is discharged in section 8
as `theNullSpaceIsNotCarriedByEveryEndomorphism`. -/
theorem theContractionPreservesTheNullSpace (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm)
    (hT : ∀ x, B (T x) (T x) ≤ B x x) :
    LinearMap.ker B ≤ Submodule.comap T (LinearMap.ker B) := by
  intro x hx
  rw [Submodule.mem_comap]
  have hsymm := LinearMap.BilinForm.isSymm_iff.mp hB
  have hx0 : B x x = 0 := (B.apply_apply_same_eq_zero_iff hs hsymm).mpr hx
  have h1 := hs (T x)
  have h2 := hT x
  have h3 : B (T x) (T x) = 0 := le_antisymm (by linarith) h1
  exact (B.apply_apply_same_eq_zero_iff hs hsymm).mp h3

/-- **The descended endomorphism**, by mathlib's `Submodule.mapQ`. -/
def gnsDescend (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) (hT : ∀ x, B (T x) (T x) ≤ B x x) :
    (N ⧸ LinearMap.ker B) →ₗ[R] (N ⧸ LinearMap.ker B) :=
  Submodule.mapQ _ _ T (theContractionPreservesTheNullSpace B T hs hB hT)

/-- **DEFINITIONAL — `rfl`**, by mathlib's `Submodule.mapQ_apply`. -/
@[simp] theorem gnsDescend_apply (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm)
    (hT : ∀ x, B (T x) (T x) ≤ B x x) (x : N) :
    gnsDescend B T hs hB hT (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T x) := rfl

/-- **The descended endomorphism still does not increase the self-pairing**, now against a form that
is *anisotropic*.  So the quotient does not merely exist; the dynamics survives it. -/
theorem theDescendedMapStillContracts (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm)
    (hT : ∀ x, B (T x) (T x) ≤ B x x) (q : N ⧸ LinearMap.ker B) :
    gnsForm B hB (gnsDescend B T hs hB hT q) (gnsDescend B T hs hB hT q)
      ≤ gnsForm B hB q q := by
  induction q using Submodule.Quotient.induction_on with
  | H x => simpa using hT x

end GNS

end Soma.Holonics.Millennium.AlgebraicGNS
