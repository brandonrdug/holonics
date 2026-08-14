# Scaling is repetition of an invariant unit, and the generator is the compact representative

**Date:** 2026-08-13
**Truth status:** `proved-standard` for the square-cube law, the diffraction bound, the Hutchinson
fixed point and the Apollonian construction; `established-bounded` for the biological invariances
cited with their sources; `interpretation` for the identifications.
**Evidence:** derivation. Nothing here is built and nothing is measured.
**Provenance:** Brandon, 2026-08-13, refining the word this project had been using loosely:

> *"'Scale' is a confusing concept, because it makes you think of a linear scaling law as if it's
> attainable, but it isn't. Scale is complex, has to be. Consider scaling up a beetle to the size of
> a human, you can't just *say it*, you have to justify the structure of the animal, because the
> anatomy does not scale like that… if you did that with a physical object it would not be
> physically stable, its internal lattices would get crushed by pressure instantly, because the scale
> of the thing that was existed in that ecosystem because it was physically capable of doing so. If
> you wanted to actually scale an animal, you would have to further found its structural anatomy to
> support it relative to the environment it exists in; that's why it's complex self-similar scaling
> and information transport mechanics, like fractals. It's not that the requirements of the scaled up
> structure would be very different from the structure of the smaller form, it's like stacking
> honeycombs for a hive, or ommatidia."*

**Canon path:** refines the self-similarity definition carried in `canon/THE_HOLOBROCHOS_SPINE.md`,
`canon/TABLET_THE_REASONING_CYCLE.md` and `CLAUDE.md`; respecifies the scale-action target in
`canon/THE_INFORMATION_ENGINE.md` §4.

---

## 1 · Linear scaling is not merely unstable. It is illegal.

The square-cube law is Galileo's, *Two New Sciences*, 1638: volume grows as `L³` while load-bearing
cross-section grows as `L²`, so stress grows as `L`. He drew the bone that would have to thicken
disproportionately. `proved-standard`. A linearly scaled beetle is crushed by its own weight before
anything else about it matters.

**And under the horizon law that failure is not a physical accident.** Across a frame boundary only a
`Ratio` — carried as a pair, never divided — or an integer `Winding` survives; `Reach`, `Flow` and
`Rank` are frame-relative and **magnitudes do not cross**. A scaling that multiplies a magnitude is
attempting to transport the one species that cannot cross a boundary.

> **The square-cube law and the horizon law are the same prohibition at two altitudes.**

`interpretation`, and it is why linear scaling is not something a receiver gets to declare.

## 2 · What scaling is: repeat the unit, whose size is not free

Brandon's honeycomb and ommatidia are the mechanism. **The unit's extent is fixed by a local
constitutive law, so growth proceeds by adding units rather than by inflating one.**

| unit | what fixes its extent | how the structure grows |
|---|---|---|
| **ommatidium** | diffraction. Below roughly ten microns a facet blurs rather than resolves, so a compound eye at human acuity would be about a metre across | add facets |
| **honeycomb cell** | the wax's mechanical properties and the bee's body | add comb |
| **capillary** | exchange across its own wall | branch the network |

The third is the one with a theory attached. **West, Brown and Enquist derive allometry's `M^(3/4)`
from exactly three assumptions**: a space-filling fractal branching network, **size-invariant terminal
units**, and minimised transport cost. The exponent is not fitted; it falls out of terminal-unit
invariance — mice and whales share capillaries. *Bounded:* the universality of `3/4` is contested in
the literature, so this is carried as the canonical derivation of the mechanism and not as a settled
exponent. **The mechanism is what this record uses.**

**So "further found its structural anatomy," in Brandon's phrase, is not extra work bolted on. It is
what scaling IS**: the added structure is more of the same unit, arranged so the load still passes
through crossings the unit can bear.

## 3 · This is the coupling's own identity, and now it is not an analogy

`research/records/2026-08-13_THE_COUPLING_IS_A_FORK_COUNT_TIMES_A_RATIO…` §1 derives

```text
   Λ(n, s) = 2ⁿ · ( C / (2ˢ · r) ) = 2^{n−s} · (C/r)      — depends only on n − s
```

Refine the grain by one octave, add one fork. **The winding changes; the ratio is untouched.** That is
*add a unit, do not stretch the unit*, written as an identity — and it is why the coupling is
scale-free for the same reason the hive is: what scales is a count, and what is held is the unit.

**Section modulus is the mechanism joining the two.** `σ = M/Z` with `Z = I/c`: the geometry of the
section decides the load, not the mass. Linear scaling holds the geometry and grows the load;
repetition holds the section and adds sections. The canon's own sentence — *equal material area does
not imply equal load response* — is the beetle.

## 4 · Fractal-packing: growth by reflection is growth by repetition

The Apollonian move deposited at `papers/source/papers/prime-archimedean-formulation-atlas/main.typ`
is `x' = Σⱼ aⱼ − x`, *"an integer-preserving reflection. Repeated reflections grow the packing."* **No
sphere is ever inflated.** A tangent one is added, and the bends stay integral.

So the packing and the honeycomb are one construction, and the reflection group decides which kind:
finite group → periodic repetition → **crystal**; infinite group → repetition self-similar at every
scale → **fractal**. That is the same condition §2 of the coupling record derives for when an image
series terminates.

## 5 · The correction this forces, and it is on this session's own claim

`…_TERMINATES_ON_A_CRYSTAL.md` §4c reads that a `GROWING` population has **no compact
representative**. **That is wrong as stated and is corrected there.**

A fractal has no compact representative *as a population*. But `H.0256`, `proved-standard`, is exactly
that the Hutchinson map `F(K) = ⋃ᵢ fᵢ(K)` is a contraction on compact sets and **has a unique fixed
compact set**. So the representative exists — **it is the generator, not a sample.**

That is Brandon's sentence made precise: *"it's not that the requirements of the scaled up structure
would be very different from the structure of the smaller form."* The generator is the same at every
scale; only the count differs.

> **Condensation of a `GROWING` population is not impossible. It changes species: retain the return
> law and the count, instead of retaining points and a certified tail.**

`interpretation`. And it sharpens the three regimes rather than dissolving them — what varies is
*what the compact representative is made of*:

```text
   SETTLED   the image series closes    representative = the finite image set, remainder is the tail
   BENT      closes, deficit reads      representative = the set, with the curvature retained
   GROWING   never closes               representative = the GENERATOR and a count, never a sample
```

`H.0256`'s own boundary keeps this honest: *"Visual recurrence does not establish a contraction
system. Dimension formulas require separation hypotheses."* A `GROWING` reading licenses looking for
a generator; it does not supply one.

## 6 · What this respecifies for construction

The scale action's carrier is **not** a magnitude and **not** a receiver horizon. It is the pair
**(invariant unit, count)** — `Λ(n,s)`'s two slots.

- The unit half already exists, typed and undivided: `cuda_aperture.rs`'s
  `CarrierDilation { arc, chord }`, with `cmp_against` ordering two of them by cross-multiplication,
  *"it never divides and never rounds."*
- The count half is absent, and so is any composition.

**The composition law, and its falsifier, in one line:** composing two scalings **adds windings and
leaves the ratio bit-identical**. If the ratio moves, the unit was stretched, and that is the beetle.

That is a materially smaller and better-specified target than *"a founded dilation action"*, and it
can fail on its first test.

## 7 · What this does not establish

It builds nothing. It does not supply a generator for any material this body holds, and `H.0256`'s
separation hypotheses are not checked anywhere. The `3/4` exponent is cited for its mechanism and its
universality is contested. And the identification of the square-cube law with the horizon law is
`interpretation`: both prohibit transporting a magnitude across a boundary, which is a shared shape
and not a proof that either implies the other.
