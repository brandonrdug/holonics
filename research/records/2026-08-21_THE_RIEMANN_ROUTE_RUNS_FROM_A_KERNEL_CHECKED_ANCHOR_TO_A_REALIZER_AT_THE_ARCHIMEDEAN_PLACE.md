# The Riemann route runs from a kernel-checked anchor to a realizer at the archimedean place

**Date:** 2026-08-21
**Kind:** a problem-specific route chart — the composition Sol's cold audit named as the next
mathematical burden: *"compose the bounded constructions into problem-specific routes whose target
is the complete classical statement, with every carrier change and imported theorem exposed."* It
is a navigation chart, not a plan: stations are founded terrain, rungs are named open constructions
with falsifiers, and **it schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
No engine source is touched; the Lean tree is read, not extended, by this deposit.
**Truth grades:** `proved-derived` for every Lean theorem cited, kernel-checked and audited free of
`sorryAx` at the 2026-08-21 cold audit; `proved-standard` for every imported classical theorem,
cited at its station; `measured` for the sieve data, carried from its source records with their
apertures; `interpretation` for the navigation readings, marked in place; `open` for every rung.
**Boundary, first because it governs everything below:** nothing in this document claims movement
on the Riemann Hypothesis. A route chart is a statement about terrain, not a result.

---

## 0. Provenance — navigation is the intermediary law, and a route is its chart

**Brandon, directly, 2026-08-21, and it is the reason this document has the shape it has:**

> *"I established this idea that intelligence and navigation itself was the intermediary law, and
> it was purely learned from experience, by traversing causality; this came up more powerfully in
> our compression discussions … the takeaway was that navigation requires iterations of traversal
> in a way that initially seems like an attempt at exhaustive searching, but then you realize that
> the mechanism points to integration/differentiation by reflection/diffusion."*

> *"The best isolated word I can use to describe intelligence is resonance, which is why we come
> back to electromagnetism and gravity curvature so often."*

> *"Recall that irreducibility and caustics signify landmarks relative to the receiver, we're
> talking about primes and non-trivial structures otherwise."*

So a route document is not a proof outline and not a schedule. It is the founded terrain between
here and the complete classical statement, with every chart transition named, so that later
traversal — by a session, a wave, or eventually the machine — rides founded ground instead of
re-founding it. The corpus's own law orders the two motions: **founding the map is induction;
reaching the shortcut across it is deduction** (the tolerance-and-navigation section of the
operating contract). The stations below are the map. The rungs are where founding is still owed.

---

## 1. The target, complete, and the anchor that makes it formal

**The classical statement:** every non-trivial zero of the Riemann zeta function has real part
one half.

**The route has a kernel-checked endpoint, which is rare and is the asset to protect.**
`soma/formal/elementary-holonics/ElementaryHolonics/Millennium/Seam.lean` proves
(`grep -n "theComposedStatementIsTheStandardOne" Seam.lean`):

```lean
theorem theComposedStatementIsTheStandardOne :
    EveryModeSitsOnTheSelfConjugateSeam ↔ RiemannHypothesis
```

against **mathlib's own `RiemannHypothesis`**, where a *mode* is a zero of the comb that is neither
a zero of the reflection's own factor nor the pole, and the *self-conjugate seam* is the fixed
locus `Fix(s ↦ 1 − s̄)`. The renaming into the composed dialect is a biconditional proved by the
fixed-locus theorem, not a paraphrase. The functional equation is imported from mathlib as
`completedRiemannZeta_one_sub` and restated as `theCompletedCombObeysTheReflectionLaw`.

Every station below must end, if the route is ever completed, at this anchor — not at a
paraphrase of it.

---

## 2. Station: placement is a fixed locus, and the open content is the realizer

**Standing, proved.** `OneInvolution.lean` proves the three fixed-locus equations on their declared
carriers:

| statement | locus | involution | theorem |
|---|---|---|---|
| Riemann | `Re s = ½` | `s ↦ 1 − s̄` | `theCriticalLineIsAFixedLocus` |
| Weil | `\|α\| = √q` | `α ↦ q/ᾱ` | `theWeilCircleIsAFixedLocus` |
| chart join | `q^s · q^{1−s} = q` | one chart apart | `theComplementaryPowersMultiplyToTheBase` |

**The imported chain that proves the Weil case** (proved-standard, function fields):

```text
ample class → polarization → Rosati involution positive → † is complex conjugation on ℚ[π]
                                                        ⊕ π†π = q  (Frobenius q-symmetry)
                                                        ⟹ |α| = √q
```

**The route's governing law, from the operating contract's realization-causes-placement section:
placement is the fixed locus of the involution a realizer induced. A returned placement that no
realizer paid for has smuggled in an absolute frame.** So the open content of RH, on this route,
is never the placement — it is the realizer, and the search for a realizer is a search for an
object, which is the question shape this project's machinery natively answers.

**Carrier change to the next station:** from zero placement in `ℂ` to positivity of a quadratic
form on a test-function space.

---

## 3. Station: the pivot from placement to positivity — Weil's criterion

**Imported, proved-standard.** Weil's explicit-formula criterion (A. Weil, *Sur les "formules
explicites" de la théorie des nombres premiers*, 1952; modern account in Bombieri's Millennium
problem description): **RH is equivalent to the positivity of the Weil functional
`W(g ∗ ḡ*) ≥ 0`** over a declared test family — a sum of local terms, one per place.

This is the station where the problem changes species: from *where are the zeros* — which, as
Brandon ruled on 2026-08-20, is posed in an absolute frame — to *does a positive form exist on a
realizer population*. The first is a predicate over a set nobody owns; the second is an object
search in a cone, with the null cone carrying the structure. The proved Weil case ran exactly this
way: `Tr(αα†) > 0` for `α ≠ 0` says the null cone of the trace form is `{0}`, and the placement
followed.

**Interpretation, marked as such:** this is the "spectral placement" half of Brandon's 2026-08-04
framing of intelligence, made precise — placement rides on a paid positivity; it is never computed
beside it.

---

## 4. Station: why the open case is open — one factor is outside the chart

**Standing in the Lean tree, with the imports named.** `Seam.lean` carries the asymmetry as
structure, not prose: the comb factors one piece per place; the pieces at the irreducibles are
rational in `p^{-s}` — algebraic; the archimedean factor `Gammaℝ s = π^{-s/2} Γ(s/2)` satisfies
**no algebraic differential equation at all** (Hölder 1886, imported), and
`theCombIsTheCompletedCombOverItsArchimedeanFactor` states the comb as the completed comb divided
by that factor, so the factor is visible *as a factor*.

**Over a function field there is no archimedean place** — every local factor is algebraic, the comb
is a rational function of `q^{-s}`, the realizer population is finite-dimensional, and Weil's
argument runs. Over the rationals exactly one factor lives outside the algebraic chart. **The route
therefore does not go around the archimedean place; it goes through it.**

Two standing facts pin where the seam sits and what the factor is:

- **The half is a half-density, not a convention.**
  `papers/source/mathematics/lemmas/mellin-half-density-chart.typ` proves `e^{u/2}` is the square
  root of the Jacobian of `r = e^u`, making the unitary rebase land the transform on the
  `Re s = ½` line. The critical line sits at the half because the archimedean factor is a
  half-density.
- **The regularized product is a condensation with no exhibited remainder.** The zeta-regularized
  `∏_{n≥0}(s+n) = √(2π)/Γ(s)` condenses the far tower into a compact representative by a declared
  quotient that discards a divergence without returning it. `Seam.lean` records this and correctly
  refuses to state a `Prop` for it while the regularized product has no definition in scope. This
  is an instance of the one organ the operating contract's missing-organ section holds open:
  **exact elimination of a far population is built (`crates/holonic-engine/src/diffusion.rs`, the
  exact rational Schur complement with both inverse residuals); a compact representative with a
  certified remainder is not.**

---

## 5. Station: the compression onto the perp — the archimedean base that exists

**Standing, July, and it was mis-carried as open for a month.**
[`research/records/2026-07-23_THE_ARCHIMEDEAN_REMAINDER_HAS_AN_AMPLITUDE_THE_PRIME_ENTERS_THROUGH_APERTURE_OVERLAP.md`](2026-07-23_THE_ARCHIMEDEAN_REMAINDER_HAS_AN_AMPLITUDE_THE_PRIME_ENTERS_THROUGH_APERTURE_OVERLAP.md)
constructs `B₂ = −P₀N₂P₀` on `ξ₀^⊥`, proves it non-negative, and takes its positive square root,
citing Connes–Consani (arXiv 2006.13771). The 2026-08-20 waves then proved the algebraic frame for
exactly this move, in `LorentzianPerp.lean`:

- `theReverseCauchySchwarzIsNonpositivityOnThePerp` — the reverse inequality against a class of
  positive self-pairing **is equivalent to** non-positivity on that class's perp;
- `theBoundedFormIsNonpositiveOnThePerp` — the two-form version, with no symmetry or
  non-degeneracy assumed, which is **why a compression `P†AP` and not a restriction is required**:
  the estimated operator need not preserve the perp, so the projection is load-bearing.

**A Sonin space is a subspace reached by a projection, and Weil positivity in this route is a
compression onto a perp** — the July authority's own reading, which the fifteen-iteration loop
recovered only at its eleventh iteration by finally reading it.

**The rungs at this station, each with its falsifier:**

| rung | falsifier |
|---|---|
| **An arithmetic construction whose contractivity follows from its construction** rather than from an assumed completed Weil sign — the sharpest of the three July items past the perp compression. | A construction whose contractivity is exhibited and whose composed positivity still requires the Weil sign as an input. |
| **The certified remainder for the archimedean condensation.** Define the regularized product; exhibit what the quotient discards as a retained object, the way `receiver_exact_compression` retains collapsed pairs with separating words. | A definition under which the discarded divergence provably admits no retained presentation compatible with the semigroup law. |
| **The reflected-positivity port at its corrected target.** The abstract Osterwalder–Schrader datum carries no exchange condition (proved by refutation, wave four); the port lands the round-trip form, its radical, and the descent trichotomy on the concrete net. | A concrete net on which the round-trip form's radical is not the null population the descent criterion names. |

---

## 6. Station: the monodromy reading of placement — carried undischarged, and it is the next theorem

**Open, and it has survived fifteen iterations and four waves without being attempted.** The
argument principle: the number of zeros inside a contour is the winding number of the function's
boundary image — **a zero count is a winding, which makes placement a monodromy statement**, the
same species as every winding this body already computes exactly. The fifteen-iterations
consolidation lists it as owed since its first iteration; nothing has moved.

This station is where "spectral placement" becomes checkable at finite level: for polynomials the
statement is formalizable now (mathlib carries the argument principle's ingredients), and the
engine's own standing defect list names the code-level twin —
`exact_analysis::polygon_winding` nets `+1/−1` and deposits no crossing, with the stated falsifier
*two different crossing populations producing the same net*. The Lean rung and the engine repair
are one object in two charts.

**Falsifier for the rung:** a formalized winding that does not agree with the zero count on a
declared finite family.

---

## 7. Station: the hand chart, its bridge, and the aperture control

**Standing.** `Hand.lean` and `Seam.lean` carry the parity chart:

- `λ(n) = (−1)^{Ω(n)}` — one half-turn per irreducible with multiplicity; `Σ λ(n)/n^s = ζ(2s)/ζ(s)`;
- `theMagnitudeClaimIsStrictlyStronger` — discharged: the refuted magnitude claims sat strictly
  above the open order claim;
- `ThePlacementAndTheHandAreOneStatement` and `ThePlacementAndTheOrientationAreOneStatement` —
  **named open `Prop`s**: the classical equivalences `RH ⟺ Σ_{n≤x} λ(n) = O(x^{1/2+ε})` and
  `RH ⟺ M(x) = O(x^{1/2+ε})` are real theorems not yet formalized, and `Seam.lean` names them as
  the next formalization target rather than assuming them;
- `theRefutedMagnitudeClaimWouldHaveSufficed` — discharged: under the bridge, the refuted magnitude
  claim would have implied the placement, so its refutation costs the placement nothing.

**The aperture control is measured on our own sieve and is a route asset, not an aside**
([`2026-08-20_LANDMARKS_AND_MODULI.md`](2026-08-20_LANDMARKS_AND_MODULI.md)): `L(x) < 0` at every
aperture we can reach — Pólya's conjecture, **which is false**, first sign change at
`906,150,257`. Our data would have confirmed a false law. Any numerical claim on this route is
evidence about its aperture before it is evidence about the subject.

**And the two gap scales decompose in disjoint charts**
([`2026-08-20_THE_TRACE_SEQUENCE_CARRIES_THE_WEIL_EXPONENT.md`](2026-08-20_THE_TRACE_SEQUENCE_CARRIES_THE_WEIL_EXPONENT.md)):
the Cramér scale `log²p` decomposes over the divisor lattice; the Riemann scale `√p·log p` over
continued-fraction convergents with the alternating unimodular hand. Measured to `2²⁴`, the
Cramér ratio holds near `0.70` while the ratio against RH's bound shrinks by half —
**RH controls the oscillation of the average, not the extremes**, which is why the
landmark-between-squares statement (Legendre) sits outside RH's reach. A route that conflates the
two scales is navigating the wrong chart.

---

## 8. The navigation reading, and what "exhaustive search" actually is on this route

`interpretation`, resting on measured terrain. The route's traversal law is Brandon's: what looks
like exhaustive search is the founding stroke of navigation, and the mechanism it points to is
integration by reflection/diffusion. The corpus already holds both halves as mathematics:

- **prime founding is the RIDE/FOUND primitive** — trial transport to the square-root frontier,
  exhaustion FOUNDs a new axis that becomes later terrain (the operating contract's landmark-law
  section);
- **the interior is an integral over its boundary and the kernel is built by reflection** —
  the exact Schur elimination in `diffusion.rs` with the harmonic-measure reading
  ([`2026-08-09_THE_INTERIOR_IS_AN_INTEGRAL_OVER_ITS_BOUNDARY_AND_THE_KERNEL_IS_BUILT_BY_REFLECTION.md`](2026-08-09_THE_INTERIOR_IS_AN_INTEGRAL_OVER_ITS_BOUNDARY_AND_THE_KERNEL_IS_BUILT_BY_REFLECTION.md));
- **a direction costs `log₂ ln N` where a position costs `log₂ N`** — the traversal-versus-digits
  measurement (outside sympy analysis, quoted with its provenance in the operating contract's
  tolerance section): navigation stores directions between landmarks, not positions of them.

Primes are landmarks — *irreducibility and caustics signify landmarks relative to the receiver* —
and the route to RH is, on this reading, the demand that the landmark field be unbiased at every
scale, which is the half-exponent's third face. None of this is a proof step; it is why the
stations above are ordered as they are.

---

## 9. What is owed on this route, consolidated

Gathered from the stations, deduplicated against
[`2026-08-20_THE_FIFTEEN_ITERATIONS_CONSOLIDATED.md`](2026-08-20_THE_FIFTEEN_ITERATIONS_CONSOLIDATED.md)
and the audit request. **None is scheduled; the roadmap alone schedules.**

| owed | station | falsifier |
|---|---|---|
| the placement↔hand bridge, formalized | the hand chart | a proof of either bridge `Prop`, or a demonstrated dependency that blocks it in mathlib's current state |
| the winding/argument-principle placement, finite level first — **INSTRUMENT RETURNED 2026-08-21**: `ElementaryHolonics/Millennium/Sturm.lean` (58 theorems) — the exact counting chain with the reading proved equal to the independently-proved root population on nine window/population pairs, the blind-entry law, the positive gauge, and the bound-versus-count gap against mathlib's Descartes rule exhibited on material; Sturm's theorem in general stays the named-open law `TheReadingEqualsThePopulation`, carried with an anti-vacuity control and the proof that it entails the independently-proved star window. What remains of this rung is the general law and the complex-winding face. | monodromy | a formalized winding disagreeing with the zero count |
| arithmetic contractivity-from-construction | perp compression | as stated at its station |
| the regularized product with a certified remainder | archimedean condensation | as stated at its station |
| the reflected-positivity port at the concrete-net target | perp compression | as stated at its station |
| the July corpus read — 288 of 292 unread, the Sonin/Weil line lives there | all | — |

## 10. Boundaries

No claim of movement on the Riemann Hypothesis is made anywhere above. The route's proved content
is: fixed-locus equivalences, the anchor biconditional, the reverse-inequality equivalence, the
magnitude/order separation, and the July perp construction — each on its declared carrier. Weil's
criterion, Hölder's theorem, the function-field chain, and the Connes–Consani estimates are
imported and cited, never reproved. The sieve figures carry their apertures and the Pólya control
governs their use. The navigation reading is `interpretation` and grades nothing.
