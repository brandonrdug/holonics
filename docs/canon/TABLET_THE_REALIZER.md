# The realizer: positivity, the holomorphic half, and rendering

> **Part of the mathematics tablet.** The spine, the quotation convention, the reading
> rule, and the law this file's sections instance are in `canon/THE_MATHEMATICS_TABLET.md`.
> Read that first; this file is one mechanism of it and is governed by it.

Hodge-Riemann where it is proved, the holomorphic organ that was already owned, and rendering as a receiver whose missed feature is an obstruction.

---

## 14. Hodge: the positive form is built where it is proved, and the holomorphic half is owned

**Truth status:** `proved-standard` for Adiprasito–Huh–Katz, Niven, and the universal-coefficient
facts; `implemented-exact` for every owner named, each opened; `established-bounded` for the two
measured absences. **Nothing in this section is a claim on the Hodge conjecture.**

### 14.1 The positive form, on the object where there is no variety at all

`crates/holonic-engine/src/matroid_chow.rs` (2,620 lines) builds the Chow ring of a simple matroid
and the Hodge–Riemann form on it. Adiprasito, Huh and Katz, *Hodge theory for combinatorial
geometries*, **Annals of Mathematics 188 (2018)**, prove that `A*(M)` satisfies Poincaré duality,
hard Lefschetz and the Hodge–Riemann bilinear relations for an **arbitrary** matroid — one that need
not be representable over any field, so there is no variety underneath it — and that HR in degree one
gives log-concavity of the characteristic polynomial, the Heron–Rota–Welsh conjecture.

That is `CLAUDE.md` §11's four-part demand on an object where every part is finite and proved:

- **supported realizer population** — the ground set and its lattice of flats;
- **exactly computed positive form** — `(a,b) ↦ (−1)^k deg(ω^{r−2k}·a·b)` on `P^k`, integral,
  finite rank, decided by elimination over `Rat`, and **able to come out wrong**;
- **reopening rule keyed to the receiver family** — `P^k = ker(ω^{r−2k+1})`, so which subspace the
  form is definite on is a function of which realizer `ω` was declared, and moving `ω` moves it.

`I` is a monomial ideal, so the degree-`k` part of `Z[x]/I` is spanned by flag monomials outright —
**no Gröbner basis is computed anywhere** — and `J` is one exact rational row reduction per grade.
`ChowRing::monomial_basis_is_integral` reports whether the reduction stayed over `Z`, which is the
certificate that the chosen monomials are a `Z`-basis rather than only a `Q`-basis.

**§2b's discipline is obeyed structurally: the module never says a form *is* positive.** It returns
the `Inertia` split, which no change of basis moves, and separately the **hand**, the declared
`(−1)^k` twist naming which cone is being called returning. `hodge_riemann_holds` is a claim about
the pair and not a property of the matrix. And there are two frames: the Lefschetz decomposition
`A^k = ⊕_j ω^{k−j} P^j` *predicts* the split on all of `A^k` from the primitive dimensions, and that
prediction is compared against what elimination returns from the full matrix. The comparison can
fail.

**§2's 2026-08-08 correction — `Eff ⊋ Amp`, positivity is supplied by ampleness and not by
supportedness — is implemented as a certificate.** `ChowRing::submodularity_verdict` (`:1138`)
decides whether a declared coefficient family is strictly submodular **before** it is used, so a
falsifier is *known* to be outside the ample cone rather than asserted to be. Measured: a strictly
supermodular family drives `deg(ω²)` negative on every rank-three fixture and breaks HR; `−ω` for
ample `ω` breaks the top grade whenever `r` is odd; and the **modular** family, which sits exactly on
the cone's boundary, does *not* break HR at these degrees — recorded as a measured finding rather
than hidden.

**The aperture is stated with counts rather than adjectives.** Ground set ≤ 9, rank ≤ 4; the rank
table is dense over `2^|E|` and the axiom audit is `4^|E|`. The Vámos matroid — rank 4 on 8 elements,
representable over no division ring — is **inside** the aperture as a matroid and **outside** it as a
ring: its top grade carries 997 chain monomials against 2,793 relation rows, and that elimination was
not run. `Matroid::vamos` and `chain_monomial_census` exist so the wall can be stated exactly.

### 14.2 The cokernel, and the model that is faithful to Kollár rather than to torsion

`supported_realizers.rs` returns `ObstructionSpecies::{Unreachable { free_rank },
ReachableOnlyInMultiple { factor }}` (`:104`) from the Smith normal form of the realizer-against-class
incidence, with the invariant factors returned as the artifact. §13.2 exhibits eighteen instances at
`factor: 2` with their cells named.

**The module audits its own positive form and says what it is worth.** `positive_form` (`:173`)
returns `MᵀM`, and the header states plainly that `xᵀ(MᵀM)x = |Mx|² ≥ 0` for *every* integer matrix
and *every* probe, so semi-definiteness is a property of the expression and never of the material —
`CLAUDE.md` §8's tautology rule applied by an owner to itself. What carries evidence is the rank, the
invariant factors, and the required-nonzero cross-check against an independently rebuilt incidence.

`placement.rs` is the composition and the entry point: a conduct class with a realizer STANDS, one
with none is OPEN and never a class. Placement is derived from realization and is not computed beside
it, which is §2's architectural demand.

### 14.3 The holomorphic half is owned, and it is aperture-complete by a theorem

**The not-yet-written list this section replaces said the holomorphic half was unwritten** — readable
at `git show HEAD:docs/canon/THE_MATHEMATICS_TABLET.md`. **That was true of the document and false of the
repository, and the code governs (§8).** `crates/holonic-engine/src/causal_reflection.rs` is a
holomorphic organ:

- **Causality is holomorphy, algebraically.** `χ(z) = Σ_n h[n] z^{−n}` is a Laurent polynomial; a
  nonzero pre-stimulus value `h[−m]` is the coefficient of `z^{+m}`, a pole at infinity. So a
  response is causal exactly when its transfer function extends holomorphically to the exterior chart
  including `∞`, where its value is the instantaneous response `h[0]`. `HolomorphyWitness` (`:885`)
  decides this by inspecting coefficients — **no half-plane, no contour, no limit.**
- **Kramers–Kronig is a pointwise sign flip.** The even and odd faces `h_e, h_o` carry `Re χ` and
  `Im χ`; multiplication by `σ[n] = sgn(n)` in the response domain is exactly what the singular
  Hilbert kernel `1/(π(ω′−ω))` is the transform of. The relation that costs an improper integral on
  one side costs a negation on the other.
- **The spectral aperture is closed by Niven's theorem, not by an implementation limit.** Both
  spectral faces are rational for every rational response exactly when every `sin(2πk/N)` and
  `cos(2πk/N)` is rational, that is exactly when `N ∈ {1,2,4}`, and the circular Hilbert kernel
  `(2/N)cot(πm/N)` is rational at the same `N`. `FourPointSpectralReflection` is therefore
  **aperture-complete by a theorem** — `CLAUDE.md` §8's rule that an aperture-complete instrument
  must say so, satisfied — and the module states its own five non-establishments, including that the
  four-point organ tests the *folded* response and exhibits a violating fixture rather than asserting
  the aperture.

`ExactReading` in `model_surface.rs:54` is the same discipline at the presentation boundary:
`RealPart`, `ImaginaryPart`, `SquaredModulus`, `HarmonicReal`, `Quadrant` — `Abs` and `Arg` refused
because `sqrt` and `atan2` are transcendental, and `quadrant_of` returns `None` at the origin because
inventing a phase there would manufacture one.

### 14.4 What is measurably absent

**There is no `(p,q)` bigrading and no Hodge decomposition in this repository.**
`crates/holonic-engine/examples/graded_complex_integer_invariants.rs:11` states it as a measurement
and its whole TSV is indexed by the single chain degree `k`. `CONSTRUCTION_STATE.md:96` carries the
position: *"`Hodge` in the live body names the cellular-sheaf Laplacian in `sheaf_diffusion.rs`, a
discrete differential operator — **not** the supported-realization mechanism. Do not read one for the
other."* So three distinct things in this tree are called Hodge — the HR form on a matroid, a sheaf
Laplacian, and the cycle-class question — and only the first is implemented as a Hodge-theoretic
object.

The missing coupling is nameable in §6's terms rather than as a missing faculty: **the complex
structure `J` exists as a chart relation (`dimensional_receiver.rs:84`) and no graded object anywhere
carries an eigenspace decomposition under it.** A `(p,q)` grading is exactly that decomposition. That
is one adapter — a graded complex whose grade-`k` part is split by a declared `J`-action — and until
it exists, no statement in this repository about Hodge classes is about Hodge classes.

---

## 15. Rendering is a receiver, and a missed feature is an obstruction

**Truth status:** `implemented-exact` throughout, owners opened; `established-bounded` for the
comparison to adaptive sampling, whose boundary the compared system documents itself.

Brandon's ruling, quoted from `docs/canon/THE_QUOTE_NETWORK.md` §8 where it is carried with its date and
transcript, 2026-08-07:

> *"I believe that for us to find our own holonic representation that is analogous to MorphoHDL, such
> that you can analyze the emergent holonic output from the machine as a grown circuit, and such that
> we can graphically render these grown circuits using perceiving receivers in order to keep
> graphical rendering correct; the idea is that the visual rendering is mathematically valuable in
> the same way that the Cartesian plane was initially valuable, not just an illustration but also
> insight into the emergent shapes that functions and differential equations literally cause."*

### 15.1 The one sentence that separates this from plotting

The established practice in mathematical graphics is adaptive sampling: evaluate on a grid,
subdivide where the result looks rough, stop at a recursion bound. Wolfram documents the consequence
on every one of its samplers — *"it is possible for Plot to miss features"* — and **a missed feature
leaves no trace in the output**, so a reader cannot distinguish a smooth curve from a curve whose
interesting part fell between two samples.

`crates/holonic-engine/src/certified_face.rs` never subdivides in hope. `IntegerPolynomial` carries an
exact Sturm sequence, so the number of distinct real roots in a rational interval is a computable
integer, and the cell law is:

```text
count == 0   the cell is certified featureless -- the segment stands, exactly
count == 1   isolate it and deposit a located feature
count >  1   subdivide, with the count itself as the termination certificate
undecided    deposit an OBSTRUCTION -- never a smooth-looking lie
```

**The obstruction population is part of the returned face.** A face that resolved everything says so
by carrying an empty one; a face that did not says exactly where it failed and how many features it
could not separate. `ReceiverWindow::initial_cells` (`:64`) carries the doc sentence that keeps this
honest: *"This is an aperture, not a quality knob: raising it does not make an unresolved cell
resolve, it only changes where the cuts fall."* And no coordinate in a returned face is authored —
every rational is a receiver-declared window endpoint or an exact value of the source polynomial.

### 15.2 The gauge cannot reach the object, and the falsifier is structural

`research/records/2026-07-13_COLOR_IS_A_RECEIVER_FACE_THE_HIGHLIGHT_IS_THE_RELATION.md` ratified

```text
T_(B,P,g) := radiation(B <- eye(P,g))     the ordered raw construction
H_G       := render_G(P, T_(B,P,g))       a human microscope beside T
```

with the binding consequence that a global change of `G` changes only the human colors and cannot
alter `T`. `presentation_gauge.rs` makes that structural rather than promised: `CertifiedFace` owns
no colour, the gauge module owns no geometry, and `render` (`:263`) takes the face by shared
reference and *cannot* mutate it. `DisplayGauge::permuted` exists solely so the falsifier can run —
render under both and every structural byte must be identical.

**And the control-design lesson is recorded in the source, which is the part worth carrying.** When
`declared` and `permuted` were both eight characters, a perturbation making mark radius depend on
`name.len()` produced byte-identical output under both gauges and the falsifier could not see it. The
names now differ in **length** as well as content. That is `CLAUDE.md` §8's rule — *a check whose
material cannot vary the property under test is the same defect as a check that cannot fail* — caught
by the rendering organ on itself.

### 15.3 Perspective is a receiver declaration all the way to the raster

- **The projection is the receiver's** (§10.2): `ProjectionLaw` and the exact pullback Gram, with the
  receiver's own gauge deciding what length one is.
- **A direction the finite chart cannot hold does not disappear.**
  `ReceiverProjectiveHorizonFiber` (`receiver.rs`) retains a horizon direction with its exact support
  contacts and native implicit roots, so clipping is a *reading* and never a loss.
- **A raster member is not a point sample.** `presentation.rs`: *"A matrix member receives every
  primitive whose support intersects its finite area; its center is never used as a surrogate ray."*
  Point-sampling a pixel is the same defect as sampling a curve, one dimension down, and the
  presentation refuses it at the same place `certified_face` refuses it.
- **Colour is derived from the receiver's own state, not assigned.**
  `examples/desktop_receiver.rs:49`: each embodied receiver's exact coordinate, momentum and net
  impulse form its contemporary phase triple; the monitor membrane subtracts the least component —
  which retains signed phase orientation — and takes exact barycentric ratios into its local RGB
  basis. RGB is the outer transducer's basis, not a colour ontology.
- **The platform is transport only.** `display.rs` packs a completed presentation; `platform.rs`
  carries integer extents and device counts; `platform_x11.rs` validates a complete batch, blits all
  runs and flushes once, and *"never owns receiver geometry, crossing formation, physical law, or
  chronology."*
- **A phase colour wheel is replaced by a stronger object, not approximated.** `model_surface.rs`
  refuses `Arg` and returns the **winding number** instead, certified by `eta_boundary_winding` from
  sign-of-cross-product ray crossings with no angle anywhere. A winding number over a closed boundary
  *counts the zeros inside, exactly*; a sampled phase field shows where a zero probably is.

```text
source geometry  ->  receiver map     ->  transport         ->  returned residual
an exact object      a declared           the exact             the located features, the
(polynomial,         window, projection   Sturm/Möller-         OBSTRUCTIONS it could not
construction,        law, gauge, and      Trumbore /            separate, and the horizon
grown circuit)       palette              pullback pipeline     fibers outside the chart
```

### 15.4 What is not done

The responsible owner exists and the applications have not all been moved onto it:
`crates/holonic-engine/examples/generative_transport_prediction.rs` and
`inverse_transport_reconstruction.rs` still hand-write an `<svg>` preamble with a hardcoded position
array and an inline palette, which `archive/plans/CONTAMINATION_BANS.md` convicts as an
application-owned codec. And there is no owner joining §15 to §13: the grown circuit Brandon names in
the ruling above is rendered by `examples/grown_circuit_schedules.rs` as text and invariants, never
through `certified_face` and `presentation_gauge`. **The rendering organ has never been pointed at
the object it was commissioned for.**

**Re-measured 2026-08-15, and it HOLDS.**
`grep -n "<svg" crates/holonic-engine/examples/generative_transport_prediction.rs crates/holonic-engine/examples/inverse_transport_reconstruction.rs`
returns `:215` and `:291` — both still hand-write the element — and
`grep -c "certified_face\|presentation_gauge" crates/holonic-engine/examples/grown_circuit_schedules.rs`
returns 0. The rendering organ's only consumers remain `src/model_surface.rs` and
`examples/certified_presentation_workbench.rs`.

---
