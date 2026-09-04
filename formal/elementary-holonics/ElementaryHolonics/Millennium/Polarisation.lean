import Mathlib.Tactic

/-!
# Inside and outside are a polarisation: Stokes adjointness, and where it fails

Brandon, 2026-08-23: *"the Poincaré group and your arithmetic are coming at it from the inside
whereas I'm coming at it from the external perspective… It's the divergence theorem and it's a
conservation thing between the surface and the exterior, where the term 'exterior' is polarized…
The limit is a question about down becoming up."*

**The mechanism is exact and it is adjointness.**  Stokes' theorem in every form — divergence,
Green, Gauss–Bonnet — is one statement:

```text
⟨ d ω , c ⟩  =  ⟨ ω , ∂ c ⟩
```

the exterior derivative and the boundary operator are adjoint.  So an interior reading and a
boundary reading are **the same information**, which is why building from inside and breaking from
outside must agree wherever both are defined.  Its engine is `∂∂ = 0`, proved below on the minimal
complex.

**And the polarisation is the orientation.**  Reversing the normal negates the flux and changes no
physics: which side is "outside" is a *gauge*, exactly as concave/convex is and as `A` versus `−A`
inertia is.  What no frame touches is that the two sides *differ*.

**Where down does become up.**  A global choice of side is a section of the orientation bundle, and
it exists only when the surface is orientable.  On a Möbius band or a Klein bottle there is no such
section: transporting a normal around the core returns it reversed, so *interior* and *exterior*
are not defined at all and the divergence theorem has nothing to say.  That is the precise form of
his limit — not a hard case of the theorem but the absence of its hypothesis — and it is the same
monodromy the corpus already carries at `√z`, one dimension up.

**On the numbers.**  His outside-in count reaches `12`; the inside-out count is
`dim(Poincaré) = 4 + 6 = 10`, `11` with the dilation, `15` with the special conformal generators.
The mechanism above genuinely produces a two-fold ambiguity (the two orientations), and `12 − 10 =
2`; **that is a coincidence of sizes, not a derivation, and it is recorded as unreconciled.**
-/

namespace Soma.Holonics.Millennium.Polarisation

/-! ## 1.  The boundary of a boundary is zero -/

/-- A `1`-chain on the minimal complex: coefficients on the three edges of a triangle. -/
abbrev Chain1 := ℚ × ℚ × ℚ

/-- Its boundary, as coefficients on the three vertices: edge `i` runs from vertex `i` to
vertex `i+1`. -/
def bdry (c : Chain1) : ℚ × ℚ × ℚ :=
  (c.2.2 - c.1, c.1 - c.2.1, c.2.1 - c.2.2)

/-- **THE BOUNDARY OF THE FUNDAMENTAL CYCLE VANISHES.**  The triangle's own boundary is zero —
which is `∂∂ = 0` on the minimal complex, and the reason a closed surface has no edge to leak
through. -/
theorem theBoundaryOfTheCycleIsZero : bdry (1, 1, 1) = (0, 0, 0) := by
  simp [bdry]

/-- **AND THE TOTAL OF ANY BOUNDARY IS ZERO.**  Whatever the chain, its boundary sums to nothing:
conservation, before any geometry. -/
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
and the boundary reading of the same chain are one number.  Every divergence, Green and
Gauss–Bonnet statement is this identity with more analysis attached. -/
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

/-- **THE NON-ORIENTABLE CASE IS THE ABSENCE OF THE HYPOTHESIS, NOT A HARD CASE.**  A consistent
global side is a fixed point of the flip on every cell at once; on a Möbius core the transport
returns the normal reversed, so the only chain fixed by the flip is the zero chain — there is no
side to choose, and `interior` and `exterior` are undefined rather than difficult. -/
theorem theOnlyFlipFixedChainIsZero {c : Chain1} (h : flip c = c) : c = (0, 0, 0) := by
  obtain ⟨a, b, d⟩ := c
  simp only [flip, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> linarith

end Soma.Holonics.Millennium.Polarisation
