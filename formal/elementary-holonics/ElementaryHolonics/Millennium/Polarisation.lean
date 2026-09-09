import Mathlib.Tactic

/-!
# Inside and outside are a polarisation: Stokes adjointness, and where it fails

Brandon, 2026-08-23: *"the Poincaré group and your arithmetic are coming at it from the inside
whereas I'm coming at it from the external perspective… It's the divergence theorem and it's a
conservation thing between the surface and the exterior, where the term 'exterior' is polarized…
The limit is a question about down becoming up."*

[proved-standard] Stokes pairs exterior change with an oriented chain boundary:

```text
⟨ d ω , c ⟩  =  ⟨ ω , ∂ c ⟩.
```

The finite theorem below is the algebraic cochain/chain pairing on a triangle. Smooth Stokes
additionally requires its differentiability, integration and orientation hypotheses. Equality of
these paired readings does not reconstruct the complete interior or remove its receiver fibre.
Boundary-of-boundary zero is a chain compatibility law; it does not alone prove smooth Stokes.
Gauss–Bonnet additionally requires its curvature and global topological construction.

[definition] Polarisation retains orientation. Reversing a chain negates its flux pairing; a
consistent rechart carries both the source and its receiver. A physical change of boundary or
material is a separate operation. The two meanings cannot be identified from a sign alone.

[proved-standard] Nonorientability obstructs a global orientation, while local oriented charts
and differential forms remain available. Integration then needs the appropriate oriented-chain,
density or orientation-local-system formulation. It does not make all interior/exterior or
boundary calculus undefined. The last theorem below is only a rational sign-flip calculation;
it constructs neither a Möbius band nor a Klein bottle. See `docs/FORMAL_FRAMEWORK.md` for the
shared exterior/boundary calculus and its actual source owners.

**On the numbers.**  His outside-in count reaches `12`; the inside-out count is
`dim(Poincaré) = 4 + 6 = 10`, `11` with the dilation, `15` with the special conformal generators.
The mechanism above genuinely produces a two-fold ambiguity (the two orientations), and `12 − 10 =
2`; **that is a coincidence of sizes, not a derivation, and it is recorded as unreconciled.**
-/

namespace Soma.Holonics.Millennium.Polarisation

/-! ## 1. Boundary cancellation on the triangle -/

/-- A `1`-chain on the minimal complex: coefficients on the three edges of a triangle. -/
abbrev Chain1 := ℚ × ℚ × ℚ

/-- Its boundary, as coefficients on the three vertices: edge `i` runs from vertex `i` to
vertex `i+1`. -/
def bdry (c : Chain1) : ℚ × ℚ × ℚ :=
  (c.2.2 - c.1, c.1 - c.2.1, c.2.1 - c.2.2)

/-- The oriented triangular cycle has zero vertex boundary. This calculation does not itself
construct a graded chain complex or prove a physical conservation law. -/
theorem theBoundaryOfTheCycleIsZero : bdry (1, 1, 1) = (0, 0, 0) := by
  simp [bdry]

/-- The vertex coefficients of an edge boundary sum to zero by incidence cancellation. -/
theorem theBoundaryConserves (c : Chain1) :
    (bdry c).1 + (bdry c).2.1 + (bdry c).2.2 = 0 := by
  simp [bdry]

/-! ## 2.  Adjointness: the interior reading and the boundary reading are one -/

/-- The pairing of a `0`-cochain with a `0`-chain. -/
def pair0 (f c : ℚ × ℚ × ℚ) : ℚ := f.1 * c.1 + f.2.1 * c.2.1 + f.2.2 * c.2.2

/-- The exterior derivative of a `0`-cochain: differences along the three edges. -/
def dcoch (f : ℚ × ℚ × ℚ) : Chain1 := (f.2.1 - f.1, f.2.2 - f.2.1, f.1 - f.2.2)

/-- The pairing of a `1`-cochain with a `1`-chain. -/
def pair1 (g c : Chain1) : ℚ := g.1 * c.1 + g.2.1 * c.2.1 + g.2.2 * c.2.2

/-- **STOKES, AS ADJOINTNESS.**  `⟨df, c⟩ = ⟨f, ∂c⟩` exactly — the interior reading of a difference
and the boundary reading of the same chain agree. Smooth integral and curvature theorems
retain their separate analytic and global hypotheses. -/
theorem theAdjointnessIsStokes (f : ℚ × ℚ × ℚ) (c : Chain1) :
    pair1 (dcoch f) c = pair0 f (bdry c) := by
  simp [pair0, pair1, dcoch, bdry]
  ring

/-! ## 3.  The polarisation is a gauge; that the sides differ is not -/

/-- Reversing the orientation of every edge. -/
def flip (c : Chain1) : Chain1 := (-c.1, -c.2.1, -c.2.2)

/-- **THE FLUX NEGATES UNDER THE FLIP.**  Which side is called outside changes the sign and nothing
else — the polarisation is a gauge. -/
theorem theFlipNegatesTheFlux (g c : Chain1) : pair1 g (flip c) = -(pair1 g c) := by
  simp [pair1, flip]; ring

/-- **BUT THE SPLIT SURVIVES.**  Flipping twice returns, so the *pair* of sides is the invariant
even though neither label is. -/
theorem theFlipIsAnInvolution (c : Chain1) : flip (flip c) = c := by
  simp [flip]

/-- And a nonzero flux stays nonzero under the flip: the two sides genuinely differ, whichever is
called which. -/
theorem theSidesGenuinelyDiffer {g c : Chain1} (h : pair1 g c ≠ 0) : pair1 g (flip c) ≠ 0 := by
  rw [theFlipNegatesTheFlux]
  exact neg_ne_zero.2 h

/-! ## 4.  Where the hypothesis fails -/

/-- Over the rational chain carrier, only zero is fixed by global sign reversal.
This is an algebraic control, not a classification of nonorientable manifolds. -/
theorem theOnlyFlipFixedChainIsZero {c : Chain1} (h : flip c = c) : c = (0, 0, 0) := by
  obtain ⟨a, b, d⟩ := c
  simp only [flip, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> linarith

end Soma.Holonics.Millennium.Polarisation
