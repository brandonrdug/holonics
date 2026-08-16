# Weil positivity is a trace on a retained remainder, and a proof transport is a one-bit compression

**Date:** 2026-08-16
**Truth status:** `proved-standard` for the classical mathematics; `interpretation` for the
correspondences and the compression reading; `established-bounded` for the measured returns.
**Evidence:** `measured` for every figure; classical statements cited to their sources.
**Occasion:** Brandon, 2026-08-16, on RH and the Hodge conjecture, and on whether the "preservation of
a property under transport" that RH needs is this repository's compression law. **Three dispatches on
this thread were in flight when this was written; their returns are not in it.**

---

## 0. His governing framing, and it decides how the Millennium problems are to be used here

> *"I don't personally care about what the truths of the Millennium problems are as conjectures in the
> sense that I need the specific way the problems are posed to be what we are concerned with, it's
> more so that what the problems are concerned with is something that holonics is equally concerned
> with somewhere in the framework, because holonics by definition has to constitute everything that
> does exist as a framework."*

**So the framework needs the OBJECTS, not the verdicts** — positive forms, realizer populations,
cokernels, fixed loci. Those exist whichever way the conjectures fall, which is why the
counterexamples have been more useful here than the conjectures.

## 1. The Hodge conjecture, in his vocabulary — ratified by him the same day

A **Hodge class** is `α ∈ H^{2k}(X,ℚ) ∩ H^{k,k}(X)`: a rational class sitting in the middle piece of a
decomposition that is itself a **receiver's** splitting by holomorphic type. An **algebraic cycle
class** is a **supported realizer** — an actual subvariety under it.

> **The Hodge conjecture is the claim that receiver-visible balance always has something supporting
> it.** Brandon: *"that interpretation of the Hodge conjecture in my vocabulary is exactly how I was
> thinking about it."*

**And the machine already exhibits one.** `substitution_realizer_placement` returns, on the hollow
tetrahedron:

```text
    OPEN  class 8   f012 f013
          reached only as 2·c — rational, not integral
          rank 1   invariant factors [2]   free obstruction 10   torsion obstruction [2]
```

A conduct class the realizer population reaches **only in a multiple** — a cokernel element, computed
exactly, with the receiver family that saw it declared.

**The framework relies on Hodge's shape and is not staked on its truth.** The **integral** statement is
false, by two independent families — torsion (Atiyah–Hirzebruch, sharpened by Totaro and
Soulé–Voisin) and **non-torsion** (Kollár: `H⁴(X,ℤ) ≅ ℤ` torsion-free, the failing class of infinite
order, `pα` algebraic and `α` not). The uniform object is the **cokernel of the cycle class map**, and
`ObstructionSpecies::ReachableOnlyInMultiple { factor }` is a type for it. Degrees 0, 2 and 2n are the
only integral cases; degree 2 is Lefschetz on (1,1)-classes and is a **ℤ**-linear theorem. And
Voisin 2002 — compact complex tori with Hodge classes not in the ℚ-span of Chern classes of **any**
coherent sheaf — is the strongest evidence for *realization pays*, because dropping the ample class
(projective = Kähler + an integral positive class, Kodaira) destroys the conclusion.

**Standing bar, unchanged:** `ReachableOnlyInMultiple` models the failed *integral* statement and
vanishes after tensoring with ℚ, so it may never be reported as a Millennium-Hodge obstruction.

## 2. Two corrections to how Weil positivity was being read

**It is not preservation of the real part as `1/2`.** It is the positive semi-definiteness of a
**form**. Weil's criterion: RH holds iff the quadratic form attached to the explicit formula satisfies
`W(f * f̄*) ≥ 0` for every admissible test function — a form with trivial radical.

**And the direction is the reverse of "preservation."** Positivity does not *preserve* the placement,
it **produces** it. That is `CLAUDE.md` §2's ruling — *placement is the fixed locus of the involution
that a realizer induced* — and the reason placement and lifting may not be built as two organs.

## 3. What a "transition" is, in the chart where it is proved

```text
    an ample divisor class  L
          ↓                        a choice — the ONLY place positivity enters
    the polarization        φ_L : J → Ĵ
          ↓
    the Rosati involution   † : α ↦ φ_L⁻¹ ∘ α̂ ∘ φ_L
          ↓                        Tr(α α†) > 0 for every α ≠ 0
    † is complex conjugation on ℚ[π]    ⊕    π†π = q
          ↓
                            |σ(π)| = q^{1/2}
```

The transition is not a map between two statements of RH. It is a **construction that produces the
placement from a realizer.**

## 4. A proof transport is a compression onto a one-bit receiver family

Brandon: *"you're talking about computational transport and codec transitions, which is what a proof
in mathematics mechanically & physically is."* That is correct, and it sharpens:

**A compression's decoder must return the MATERIAL. A proof's decoder need only return the VERDICT.**

> **So a proof transport is a compression onto a one-bit receiver family — the receiver that sees only
> *does this hold*. Everything else may be destroyed.**

Which yields the demand: **name what the transition deleted and show the predicate is not in it.** A
chart in which RH is easy is worthless until the collapsed population provably excludes the property.
That is the same obligation `H.0463`'s translation portal already states — map each named structure
and **prove preservation of the selected laws**.

## 5. The Weil route is a REBASE, not a compression

Run it through the three species, which differ only by remainder:

```text
    material           the correspondence algebra of the curve
    codec pivot        the polarization — it makes the algebra a NORMED object
    declared decoder   the Rosati involution, which returns the norm
    the invariance     positivity: the pairing's null cone is {0}
    the remainder      ZERO
```

`Tr(α α†) > 0` for every `α ≠ 0` says the form is definite, its radical is `{0}`, and **no pair is
identified**. By the corpus's own table that is a **rebase**.

> **RH-in-that-chart holds because the remainder is empty**, and an off-line zero would be a member of
> a nonzero collapsed population — a correspondence that **self-pairs to nothing**.

Which is §2b's reading exactly: *the null cone is the vacuous difference*. Positivity says **no nonzero
passage is dark to itself.**

## 6. The `1/2`, derived, and it answers `2^{e^{iπ}}`

Brandon wrote `1/2` as `2^{e^{iπ}}` — *two to the half-turn*.

`π†π = q` is `α·ᾱ = q`, so `|α|² = q`, so `|α| = q^{1/2}`.

> **The `1/2` is never a chosen constant. It is the exponent at which a thing meets its own
> conjugate.**

And both statements are one fixed locus of one species of **anti-linear** involution:

```text
    Re(s) = 1/2      is   Fix( s ↦ 1 − s̄ )
    |α|  = q^{1/2}   is   Fix( α ↦ q / ᾱ )
```

The first is supplied by the functional equation `ξ(s) = ξ(1−s)` together with `ζ(s̄) = conj ζ(s)`;
those two involutions generate a Klein four-group and the composite anti-linear one has fixed locus
**exactly** `Re(s) = 1/2`. **That much is a theorem, not a conjecture.** RH is the separate claim that
the zeros sit on it. Same `1/2` as `√x = x^{2^{-1}}`, where the `±` is the half-turn squaring erased.

## 7. What is missing for ℚ, and it makes RH and Hodge one shape

For ℚ there is **no curve, no Jacobian, no Frobenius, no ample class**. The explicit formula supplies a
distribution whose positivity is equivalent to RH — so the **pairing exists analytically** — and there
is **no realizer population underneath it**.

> **The codec exists and the material does not.** A declared decoder shape with nothing to decode.

Which is the Hodge situation one level over. So:

> **RH-for-ℚ and Hodge are the same shape: a positive form wanting a realizer population.** In the
> function-field chart the population exists, the form is definite, the pivot is a rebase, and the
> placement follows. For ℚ, and for a general Hodge class, the population is what is missing.

`CLAUDE.md` §11 already asserts this identification; what is added here is the derivation rather than
the assertion.

## 8. Connes–Consani makes the compression reading literal, not analogical

Brandon supplied **arXiv:2006.13771, Connes & Consani, "Weil positivity and Trace formula, the
archimedean place."** Its abstract states that positivity originates from

> *"the trace of the scaling action **compressed onto the orthogonal complement of the range of the
> cutoff projections**"*

with the difference between the Weil distribution and the Sonin trace expressed through **prolate
spheroidal wave functions**, hermitian Toeplitz matrices as the tool, and the conclusion that in the
semi-local case **Weil positivity implies RH**. The paper establishes positivity at the archimedean
place; the semi-local case remains conditional.

**Four words there are this corpus's own objects, and whether they are the same objects is the open
question three dispatches were sent to settle:**

```text
    cutoff projection              an APERTURE?
    orthogonal complement          a RETAINED REMAINDER?
    scaling action                 the additive→multiplicative REBASE, dx ↔ dx/x?
    prolate spheroidal functions   the eigenbasis of a DOUBLE aperture?
```

**And one of them must be checked against a standing refusal.** `canon/THE_INFORMATION_ENGINE.md`
refuses every uncertainty-relation / Gabor / time-bandwidth framing, replacing it with the
collapsed-pair population of a declared receiver family. Prolate spheroidal functions are the exact
eigenbasis of simultaneous time-and-band limiting. **Whether they fall under that refusal or are
exempt as an exact spectral construction rather than an inequality is a question that must be answered
precisely, because getting it wrong in either direction is a defect.**

## 9. What the machine returned on this thread, measured 2026-08-16

**The critical strip, with no known zero accepted as input** —
`crates/relational-geometry/examples/holonic_eta_ratio_atlas.rs`, by certified boundary winding:

```text
    zero 0  τ = [113/8, 905/64]      = [14.125,    14.140625]     root_winding 1
    zero 1  τ = [1345/64, 673/32]    = [21.015625, 21.03125]      root_winding 1
    zero 2  τ = [25, 1601/64]        = [25,        25.015625]     root_winding 1
    zero 3  τ = [1947/64, 487/16]    = [30.421875, 30.4375]       root_winding 1
    zero 4  τ = [2107/64, 527/16]    = [32.921875, 32.9375]       root_winding 1
```

Every enclosure contains the true ordinate (14.134725, 21.022040, 25.010858, 30.424876, 32.935062),
and each winding of 1 says *simple*. It also returns the **exact projective cross-ratio of four
consecutive zeros** — `[417695/267264, 420291/264668]` — which is the one projective invariant four
points on a line possess, and the first reading beyond the line itself.

**And `ψ(x) − x`, exactly** — `crates/holonic-engine/examples/prime_emergence_observatory.rs`:

```text
    founded_prime_population     54 of 255                    π(256) = 54
    chebyshev_log_coefficients   {2:8, 3:5, 5:3, 7:2, 11:2, 13:2, then 1 above √256}
    chebyshev_product_lcm        lcm(1..256), exactly
    formal_chebyshev_departure   log(lcm(1..256)) − 256
    zeta_cut_return_closes       true
```

Those coefficients are **von Mangoldt's Λ**, and `lcm(1..x) = e^{ψ(x)}`, so the departure **is
`ψ(x) − x`** — the prime-counting error term RH controls. Computed over integers, no float.

**The section-modulus instinct lands here.** `S = I/c` says strength lives in the distribution about
the neutral axis, not the total area. For zeta the axis is the critical line and the load is carried by
the **moments about it** — Montgomery's pair correlation, Odlyzko's GUE statistics, and
`∫₀^T |ζ(½+it)|^{2k} dt` with Keating–Snaith. The cross-ratio above is the first such invariant this
machine returns.

## 10. Two identifications named for the record

**The identity for chart transitions is the homomorphism law** `exp(a+b) = exp(a)·exp(b)` — what makes
something a chart transition rather than a statistic. The Jacobian is its derivative; the cocycle
condition `g_ij·g_jk = g_ik` is the same law at the atlas level.

**The fifteen are Schwarz's list**, the finite-return-group rows of the three-site turning equation,
which `hypergeometric_closure.rs` recovers 15 of 15 by sorting integers under every restretching.

## 11. A note on provenance, since it was supplied as context

Anthropic's published account of an unreleased research model attempting RH reports improving a known
lower bound on the fraction of zeros satisfying RH from 41.6% to 67.2%, validated by two
mathematicians and formalised in Lean, **with the explicit caveat that the techniques are not expected
to prove RH**. It is reported here as provenance for the working posture Brandon supplied it for and
for nothing else; no claim in this record depends on it.

---

## 12. What this record does not schedule

`blueprint/THE_ROADMAP.md` and `CONSTRUCTION_STATE.md` remain the only construction authorities.
Nothing here grades a deed, and §8's four identifications are open questions rather than findings.
