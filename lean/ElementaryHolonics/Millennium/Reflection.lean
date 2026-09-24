import ElementaryHolonics.Millennium.Ricci
import Mathlib.Tactic

/-!
# Reflection: the interior is eliminated onto its boundary, and the kernel is built by images

Integration by reflection had no Lean owner until this file — the tree's other reflections are
the conjugate reflection of the seam, the half-turns of the swing, and reflected *positivity*,
which are different objects.  The Rust owner is exact and is not rebuilt here:
`crates/holonic-engine/src/diffusion.rs` computes the boundary transport (the Schur complement)
over `Rat` with both inverse residuals retained and the killed share exhibited; the derivation
is the record *the interior is an integral over its boundary and the kernel is built by
reflection* (2026-08-09).  What this file adds is the mechanism at kernel-checked grain, and —
per Brandon's direction that the integration is a **diffusing transport chain** — its pairing
with the diffusion flow already in this tree (`Ricci.lean`).

**The load-bearing design decision answers the "arbitrary definition" worry directly: the
boundary is a DECLARED PARTITION, never an intrinsic property.**  The object is the pair
(operator, declaration); every theorem is relative to the declaration; and the relativity is
itself a theorem — two declarations over one operator give two different boundary transports,
both exact.  The implicit/contextual character of the integral's boundary is not a defect to
hide; it is receiver relativity, stated.

What is proved, all exact over `ℚ` or by kernel enumeration:

* **the interior is eliminated exactly** (one declared interior site, symbolic): the interior
  equation is solved in closed form, and the boundary row factors as the Schur-transported
  operator plus the **transported source** — the interior's cause carried to the boundary with
  its exact weights `c₁/m, c₂/m`, which is harmonic measure at this grain;
* **the exit weights are sub-stochastic with the killed share exhibited**: with capacity
  `m = c₁ + c₂ + k`, the weights sum to one *with* the killed share `k/m`, and to at most one
  without it — the sub-stochastic rows of the Rust owner, as a theorem;
* **the boundary is a declaration**: the same three-site operator under the opposite
  declaration yields a different transport entry (`5/3 ≠ 5/2` on the exhibited instance), both
  eliminations exact — the partition is the receiver's, not the operator's;
* **the kernel is built by reflection**: on ±1 walks absorbed at zero, the surviving kernel
  equals the free kernel **minus the reflected-source kernel** — Dirichlet's image with its
  minus sign — proved by kernel enumeration on six instances spanning `a, b ∈ {1,2,3,4}`,
  `k ∈ {4,6}`, each verified independently before encoding; the general reflection principle is
  a named-open proposition, never assumed;
* **the pairing with the diffusing chain**: on `Ricci.lean`'s triangle flow with one site
  declared interior and held at its equilibrium, the interior **stays** equilibrated, the
  elimination is exact, and the reduced two-site chain runs at the **renormalized aperture**
  `3τ/2` while carrying the **same winding rate** `1 − 3τ` the full flow's deviation carries
  (`theDeviationContractsAtTheWindingRate`) — coarse-graining as exact elimination, which is
  the finite shadow of the renormalization step in the Poincaré record's schema, where the
  heat kernels of the conjugate flow are built by exactly this image construction.

**Refused / not claimed:** no continuum limit, no harmonic-measure limit (the Rust owner's
`M = C + τL` is a resolvent and its own docstring says so), no Neumann face (a reflecting walk
is a different constitutive law, owed separately), and nothing about Perelman's theorem — the
pairing names a shared mechanism at finite grain.  The hypergeometric closure, Sturm isolation,
and monodromy placement remain Rust-only; their Lean line is owed and is named in the record,
not here.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.Reflection

open Soma.Holonics.Millennium

/-! ## 1. The declared interior, eliminated exactly -/

/-- The closed-form interior solve: one declared interior site of capacity `m`, coupled to two
boundary sites with conductances `c₁, c₂`, carrying source `f`. -/
def interiorSolve (c₁ c₂ m u₁ u₂ f : ℚ) : ℚ := (c₁ * u₁ + c₂ * u₂ + f) / m

/-- **The interior equation is solved exactly**: the reconstruction is closed-form, which is
the retained inverse testimony — nothing about the interior is forgotten by the elimination. -/
theorem theInteriorIsReconstructedExactly (c₁ c₂ m u₁ u₂ f : ℚ) (hm : m ≠ 0) :
    -c₁ * u₁ + m * interiorSolve c₁ c₂ m u₁ u₂ f - c₂ * u₂ = f := by
  simp only [interiorSolve]
  field_simp
  ring

/-- **The boundary row factors through the Schur transport plus the transported source**: the
first boundary row of the full operator, with the interior eliminated, is the transported
diagonal `p − c₁²/m`, the transported coupling `−c₁c₂/m`, and the interior source carried to
the boundary with weight `c₁/m` — the interior's cause arriving at the boundary through its
exact harmonic weight. -/
theorem theBoundaryRowCarriesTheTransportAndTheSource (p c₁ c₂ m u₁ u₂ f : ℚ) (hm : m ≠ 0) :
    p * u₁ - c₁ * interiorSolve c₁ c₂ m u₁ u₂ f
      = (p - c₁ ^ 2 / m) * u₁ - (c₁ * c₂ / m) * u₂ - (c₁ / m) * f := by
  simp only [interiorSolve]
  field_simp
  ring

/-- **The exit weights are sub-stochastic and the killed share is exhibited**: with capacity
`m = c₁ + c₂ + k`, the two exit weights and the killed share sum to one exactly, and the exit
weights alone stay below one — the killed share is retained, never normalised away. -/
theorem theExitWeightsAreSubStochastic (c₁ c₂ k : ℚ)
    (hk : 0 ≤ k) (hm : 0 < c₁ + c₂ + k) :
    c₁ / (c₁ + c₂ + k) + c₂ / (c₁ + c₂ + k) + k / (c₁ + c₂ + k) = 1 ∧
    c₁ / (c₁ + c₂ + k) + c₂ / (c₁ + c₂ + k) ≤ 1 := by
  constructor
  · field_simp
  · have hkm : 0 ≤ k / (c₁ + c₂ + k) := div_nonneg hk (le_of_lt hm)
    have hsum : c₁ / (c₁ + c₂ + k) + c₂ / (c₁ + c₂ + k) + k / (c₁ + c₂ + k) = 1 := by
      field_simp
    linarith

/-! ## 2. The boundary is a declaration -/

/-- **The boundary is a declaration, not a property of the operator**: on the three-site
operator with `p = 2, m = 3, q = 2, c₁ = c₂ = 1`, declaring the middle site interior transports
the first diagonal to `5/3`; declaring the first site interior transports the middle diagonal
to `5/2`.  Both eliminations are exact by the theorems above; the transports differ.  The
"implicit, contextual" boundary of the integral is receiver relativity, stated. -/
theorem theBoundaryIsADeclaration :
    (2 : ℚ) - 1 ^ 2 / 3 = 5 / 3 ∧ (3 : ℚ) - 1 ^ 2 / 2 = 5 / 2 ∧ (5 : ℚ) / 3 ≠ 5 / 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## 3. The kernel is built by reflection -/

/-- Free walk endpoints: all `±1`-step positions after `k` steps, with multiplicity. -/
def freeWalks : ℕ → ℤ → List ℤ
  | 0, a => [a]
  | k + 1, a => (freeWalks k a).flatMap fun p => [p + 1, p - 1]

/-- Absorbed walk endpoints: as above, but a walk dies the moment its position leaves the
positive half-line — the Dirichlet boundary at zero. -/
def aliveWalks : ℕ → ℤ → List ℤ
  | 0, a => [a]
  | k + 1, a => (aliveWalks k a).flatMap fun p => ([p + 1, p - 1].filter fun q => 0 < q)

/-- The free kernel: the number of `k`-step walks from `a` landing at `b`. -/
def freeKernel (a b : ℤ) (k : ℕ) : ℕ := ((freeWalks k a).filter fun p => p == b).length

/-- The absorbed kernel: as above, surviving the Dirichlet boundary. -/
def absorbedKernel (a b : ℤ) (k : ℕ) : ℕ := ((aliveWalks k a).filter fun p => p == b).length

/-- **The kernel is built by reflection** — the absorbed kernel is the free kernel minus the
kernel of the reflected source, on six instances spanning the small aperture; each side is
enumerated by the kernel, and each instance was verified by an independent enumeration before
encoding.  The image carries the minus sign because the boundary is absorbing: the sign **is**
the boundary condition. -/
theorem theKernelIsBuiltByReflection :
    (absorbedKernel 1 1 4 : ℤ) = freeKernel 1 1 4 - freeKernel (-1) 1 4 ∧
    (absorbedKernel 1 1 6 : ℤ) = freeKernel 1 1 6 - freeKernel (-1) 1 6 ∧
    (absorbedKernel 2 2 4 : ℤ) = freeKernel 2 2 4 - freeKernel (-2) 2 4 ∧
    (absorbedKernel 1 3 4 : ℤ) = freeKernel 1 3 4 - freeKernel (-1) 3 4 ∧
    (absorbedKernel 2 4 6 : ℤ) = freeKernel 2 4 6 - freeKernel (-2) 4 6 ∧
    (absorbedKernel 3 1 6 : ℤ) = freeKernel 3 1 6 - freeKernel (-3) 1 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- **The general reflection principle**, named open and never assumed: for every positive
source and target, the absorbed kernel is the free kernel minus the reflected one.  Classically
André's reflection; the bijection sends a touching walk to its prefix-reflected image. -/
def TheReflectionPrincipleHolds : Prop :=
  ∀ (a b : ℤ) (k : ℕ), 0 < a → 0 < b →
    (absorbedKernel a b k : ℤ) = freeKernel a b k - freeKernel (-a) b k

/-! ## 4. The pairing with the diffusing chain -/

/-- **The equilibrated interior stays equilibrated**: on the triangle flow with the third site
held at the mean of the boundary pair, one flow step preserves the equilibrium — the declared
interior is stationary relative to its boundary, which is what makes the elimination lawful on
the flow. -/
theorem theEquilibratedInteriorStaysEquilibrated (τ a b : ℚ) :
    (Ricci.flow τ (a, b, (a + b) / 2)).2.2
      = ((Ricci.flow τ (a, b, (a + b) / 2)).1 + (Ricci.flow τ (a, b, (a + b) / 2)).2.1) / 2 := by
  simp only [Ricci.flow]
  ring

/-- **Eliminating the interior renormalizes the aperture**: on the equilibrated locus the
boundary pair's step is exactly the two-site averaging flow at aperture `3τ/2` — the eliminated
site does not vanish, it re-enters as a stronger coupling between the survivors.  This is
coarse-graining as exact elimination: the renormalization step of the Poincaré schema at the
grain where nothing is discarded. -/
theorem theEliminationRenormalizesTheAperture (τ a b : ℚ) :
    (Ricci.flow τ (a, b, (a + b) / 2)).1 = (1 - 3 * τ / 2) * a + (3 * τ / 2) * b ∧
    (Ricci.flow τ (a, b, (a + b) / 2)).2.1 = (1 - 3 * τ / 2) * b + (3 * τ / 2) * a := by
  constructor <;> (simp only [Ricci.flow]; ring)

/-- **The reduced chain carries the same winding rate**: the boundary pair's deviation
contracts at exactly `1 − 3τ` — the rate `theDeviationContractsAtTheWindingRate` proves for the
full triangle — so the elimination changed the aperture and preserved the spectrum's reading.
The invariant is visible across the two frames, which is what makes it an invariant. -/
theorem theReducedChainCarriesTheSameWindingRate (τ a b : ℚ) :
    (Ricci.flow τ (a, b, (a + b) / 2)).1 - (Ricci.flow τ (a, b, (a + b) / 2)).2.1
      = (1 - 3 * τ) * (a - b) := by
  simp only [Ricci.flow]
  ring

end Soma.Holonics.Millennium.Reflection
