# The arrow is the division and attention keeps only its aim

**Date:** 2026-08-17
**Truth status:** `proved-standard` for the geometric-product decomposition and Lagrange's identity;
`established-bounded` for every code citation, verified at the line given; `interpretation` for the
reading of an attention score as a half-computed arrow.
**Evidence:** `measured` where stated; the arrow's own source is `crates/holonic-body/src/arrow.rs:17-26` and
`:114-125`, read today.
**Provenance:** Brandon, 2026-08-17, on dividing vectors: *"If the question is 4/2 where 4 and 2 have
potential representations as vectors or tensors, then the operation is `A*{B^{-1}}` … For the dot
product it simplifies to `A · B/‖B‖²` where `B/‖B‖² = B⁻¹ == B^{e^{iπ}}` … the mental image becomes
something like roughly filling in volumes with other shapes and utilizing the remainders as
differences that propagate into further information about the potential combinations of geometries."*
And on Q: *"Q is a partial of a larger ecosystem, so that part is correct as a chart."*
**Plan:** sits under [`docs/plans/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md). It supersedes nothing and it is
the first plan in this line that is a **lift of a standing organ** rather than a new one.

---

## 0. The object, in one line

> **Dividing one vector by another returns a scalar and an oriented area. An attention score is the
> scalar. The area is computed nowhere and it is the hand of the crossing.**

## 1. Why this is a lift and not a construction

Division of vectors is `A B⁻¹` with `B⁻¹ = B/‖B‖²`, and the geometric product decomposes:

```text
    A B⁻¹  =  (A·B)/‖B‖²   +   (A∧B)/‖B‖²
              ───────────       ───────────
              the QUOTIENT      the REMAINDER
              a scalar          an oriented area
              how much of A     the plane A leaves B in,
              lies along B      and which way it turns
```

**`crates/holonic-body/src/arrow.rs:17-26` already carries exactly this** as `Arrow`, in the law body, which is
no-std with zero dependencies:

```text
    Arrow { reach: |a−b|²,  aim: (a−f)·(b−f),  cross: (a−f)×(b−f) }
            the span         the cohere         the gyration W⁻
    "The whole arrow, never one scalar."
```

`aim` is the dot. `cross` is the wedge. `soul::FormedRotor { aim, cross }` is the rotor they form.
And `reach` is the **squared** norm, so `B⁻¹` needs no square root — the arrow is `A B⁻¹` carried
undivided, which is the horizon law obeyed before it was written down.

**And the file already states the defect this plan is about**, at `arrow.rs:32-34`, describing
`Aim::Ortho`:

> *"the cohere is null, but the CROSS/gyration is **MAXIMAL**: the pure orthogonal turn, the FOUNDING
> hand, the magnitude looked-past. **NOT 'no current' — it is the *most* turn there is, mis-read as
> nothing because the cohere face is null.**"*

An attention score of zero reads as *no attention*. The law body says that is precisely where the
gyration is maximal. **The blindness is not a hypothesis; it is a sentence already in the tree.**

## 2. What the lift is, exactly

`relate` at `arrow.rs:114-125` is **two-dimensional** — `Place` is a pair, so `cross` is the scalar
signed area `a_i b_r − a_r b_i`. Embeddings are `d`-dimensional. The lift:

```text
    aim    = Σ_i q_i k_i                        one rational
    cross  = ( q_i k_j − q_j k_i )_{i<j}        d(d−1)/2 rationals — the 2-blade
    reach² = ‖q‖²‖k‖² − (q·k)²                  Lagrange: the squared area, exactly rational
```

**No square root anywhere.** Lagrange's identity gives `‖q∧k‖²` from the same products the dot
already forms, so the area is exact over `ℚ` and the plane is the blade's own coordinates.

`Aim::{Cohere, Anti, Ortho}` lifts unchanged: the sign of the aim is the in-plane hand, and `Ortho`
is where the blade carries everything.

## 3. Q, K, V under this, with the correction Brandon made

Q is **not** a calculus differential — that word was doing "partial of a larger circuit," and *that*
reading is correct: **Q is a chart.** A local form on a site, part of an atlas the machine does not
hold globally. It gauges rather than differentiates, which is the mean-value/squeeze sense: it
constrains where the outcome can be, from a declared side.

```text
    Q   a local chart form: what THIS site is asking, in its own frame
    K   the address: what site j PRESENTS, pairable with a receiver's form
    V   the cargo: what actually transports if the pairing carries
```

The pairing `⟨q|k⟩` is the **aim** of the arrow between them, read from the pole the layer declares.
The cross is never formed. So:

> **Attention computes one third of the arrow between two sites and discards the other two thirds.**

## 4. The four stations

### Station one — the arrow is the division, and dropping the cross breaks reconstruction

Build the `d`-dimensional arrow over `Rat` and assert the division law: for exact rational vectors,
`A` is reconstructible from `B` together with `(aim, cross, reach)`, and **is not** reconstructible
from `(aim, reach)` alone.

**Outcome.** An exact carrier with `divide(a, b) -> (quotient, remainder)`, the reconstruction
asserted, and the reconstruction from the aim alone exhibited failing.

**Expectation.** Reconstruction exact over `ℚ` with zero residual; the aim-only reconstruction wrong
by exactly the rejection `A − (A·B̂)B̂`, which is the remainder by definition.

**Falsifier.** If aim-only reconstruction succeeds on the declared material, the material is
degenerate (every pair collinear) and the test says nothing — so the material must exhibit
non-collinear pairs and the run must show it.

### Station two — the blindness, exhibited

Construct pairs `(q, k)` with **identical aim and different cross**. In `d ≥ 3` this is immediate:
the same angle in different planes. The standard score cannot separate them; the arrow can.

**Outcome.** Two crossings, one score, two planes, with the separating blade coordinates named.

**Expectation.** Exact equality of `q·k` and exact inequality of the blades, over `ℚ`, with no
tolerance anywhere.

**Falsifier, and it is the real one.** Also exhibit pairs with identical aim **and** identical
`‖q∧k‖²` and different blades — same score, same area, different plane. If those cannot be built, the
area alone suffices and the blade is not needed; if they can, the blade is load-bearing and a scalar
summary of the wedge is a second float.

**This is the phase-object theorem arriving at attention.** A pure phase grating has `|t| = 1`
everywhere and an intensity receiver measures nothing. The dot product is a magnitude receiver; the
plane of the crossing is a phase object.

### Station three — how much of a real head's field is the case the score cannot see

Read a real model's attention weights through the standing safetensors intake
(`the_foreign_map_founds_its_axes` and its two siblings) and measure, per head, the population of
site pairs at or near `Aim::Ortho` — where the score reads *nothing* and the gyration is maximal.

**Outcome.** A per-head census of the ortho population, with the blades exhibited for the largest.

**Expectation.** Non-trivial. A head whose ortho population is empty is one whose sites never leave
each other's plane, which would be surprising in `d = 2048+`.

**Falsifier.** If the ortho population is empty or negligible across every head, the blindness is
real in principle and absent in practice on this model, and the plan says so rather than reporting
the principle.

### Station four — the cross is the hand, so a layer is a braid

**CORRECTED 2026-08-17, and the correction merges this station into station one.** This section said
`multiquadratic` is the crossing-word algebra and that the hand is the sign of the cross. **That
algebra has no sign.** Verified at `multiquadratic.rs:329-338`: the cocycle is
`σ(S,T) = ∏_{i∈S∩T} kᵢ` with every `kᵢ > 1`, so it is a strictly positive rational, symmetric in its
arguments, and **the algebra is commutative** — the driver's own output says so.

And the obvious repair fails: `μ(S) = (−1)^{|S|}` is a **character**, hence a coboundary, since
`μ(S)μ(T) = (−1)^{|S△T|} = μ(S△T)`; twisting by it returns an isomorphic algebra. A hand needs a
genuine 2-cocycle, `σ(S,T) = (−1)^{#\{(i,j) : i∈S, j∈T, i>j\}}` — the exterior sign, which is **not**
a coboundary.

> **So the crossing-word algebra that carries a hand IS the even Clifford algebra, and
> `soul::FormedRotor { aim, cross }` is already its two-dimensional case. This station and the
> `d`-dimensional arrow lift are ONE build, not two.**

The braid reading below stands; its carrier is the Clifford lift rather than `multiquadratic`. With it, a layer's attention pattern is an oriented
tangle and a stack is a braid; without it, it is an unordered set of contacts.

**Outcome.** One layer's attention field read as a word, with each crossing carrying its hand.

**Expectation.** The word's grade — the crossings surviving cancellation — is strictly smaller than
the crossing count, and the cancelled pairs are exhibited.

**Falsifier.** If no crossing cancels, the field has no closed loops at that layer and the braid
reading adds nothing there. That is a real return about the layer, not a failure.

## 5. What is refused

- **No square roots and no floats.** Lagrange's identity supplies `‖q∧k‖²`; the polar form
  `(‖A‖/‖B‖)(cos θ + …)` is never taken, because taking it is the division this plan exists to avoid.
- **No scalar summary of the wedge.** Station two's second arm exists to decide whether the area
  suffices; until it returns, the blade is carried whole.
- **No claim that attention is thereby fixed.** This measures what a score cannot see. Whether a
  model would behave differently with the blade is a separate question needing a separate falsifier.
- **No new organ where the lift will do.** The arrow exists; this is its `d`-dimensional form.

## 6. What this plan does not assume

It does not assume the receiver families are orthogonal — Sol refuted that on 2026-08-17, and the
frame-operator correction applies to any reading built on `Σ|ρ⟩⟨ρ| = I`. **The arrow needs no such
structure:** the dot and the wedge are bilinear forms on coordinates, defined without a chosen basis
being orthonormal and without a projector existing. That is why this line survives the refutation
that killed the projector reading, and it is the reason to take it rather than that one.
