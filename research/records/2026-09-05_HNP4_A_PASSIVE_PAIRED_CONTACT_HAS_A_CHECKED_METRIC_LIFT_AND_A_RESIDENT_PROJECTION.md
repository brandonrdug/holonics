# HNP4: a passive paired contact has a checked metric lift and a resident projection

**Date:** 2026-09-05. **Phase:** HNP4, bounded constitutive candidate, not phase completion.

## Declared chart and formal return

[definition] `HolonicOrientedSiteTransport.PassiveContact` defines one finite real Euclidean
chart. For a source observation `x`, an arrived observation `y`, and another input `z`, set
`d = x-y`, `D = ||y||²-||x||²`, `c = |D|`, `p = max(D,0)` and `N = ||d||²+c`. Its map is
`T(z) = z - 2*(dot(d,z)+p)/N * d` when `N != 0`, and identity otherwise. This is a specified
constitutive candidate. Neither a diagonal identity metric nor a source/arrival pairing is
inferred merely from equal widths or an Add node in a neural graph.

[proved-derived; formal-checked] The existing formal owner now proves:

- Matched observations return identity, and `T(x)=y`.
- `||T(z)-T(w)||² = ||z-w||² - 4*c/N² * dot(d,z-w)²` when `N != 0`, hence non-expansiveness.
- A one-axis lift with metric coefficient `c`, source axis `a=1` exactly when `D>0`, target
  axis `b=1` exactly when `D<0`, and returned axis `a-(a-b)*2*(dot(d,z)+p)/N` preserves
  `||z||²+c*a²`. In particular `||T(z)||² <= ||z||²+p`.

[definition] These are finite metric statements. Their quadratic quantity is not physical
energy without units, calibration and an actual constitutive identification. They do not prove
that an arbitrary changing sequence of such maps is a stable or useful neural learner. In
particular, non-expansiveness is a distance bound, not permission to reset a source axis and
silently introduce a fresh positive `p` on every cycle. The old additive-return counterexample
is not repaired merely by inserting this map around the same endogenous Add effect.

## Resident realization and numerical boundary

[established-bounded; source-inspected] `ResidentSurface::record_passive_contact` records the
map in `section_passive_contact` in the existing resident CUDA owner. Each row is a declared
independent chart. All three sections and the output must have the same nonempty shape/grain;
the two founding observations must be point intervals. The query may be an interval section.
Non-point founding observations refuse; no midpoint or application-supplied learning gain is
substituted. Inputs remain with their caller. No model state or continuing ecology is cloned.

[established-bounded; source-inspected] The block reduces the actual point difference, norm gap
and interval dot products on-device, then applies the directed quotient in parallel. Ceil-halving
retains every contribution under non-power-of-two block sizes. The candidate's accumulators,
operands, denominator and quotient are restricted to magnitude below `2^126`; the output still
must fit its signed 64-bit words. The existing exact unsigned 256-bit product supports division
when the intermediate product exceeds 128 bits but the admitted quotient fits. This changes
neither the model's carrier limit nor its cultivation law. Failure is explicit, never a clipped
or silently wrapped answer.

[definition] This kernel realizes the **projection** `T`, not the lifted-axis state. For interval
queries its outward enclosure need not be minimal: a query coordinate also enters the shared
dot product. The exact real non-expansiveness theorem is not a theorem that these enclosure
widths cannot grow. A complete conservative runtime interaction still owes the retained axis
or its exact reconstruction and successor law. No Rust/CUDA correctness theorem is asserted.

## Verification

[established-bounded; measured] The two ignored CUDA controls were explicitly run and passed:

- `passive_contact_points_calibrate_and_round_signed_wide_products`: 490 three-coordinate
  rows from seven source/arrival observations and five query placements, at grains 0 and 43.
  Every output interval matched the floor/ceiling of an independent arbitrary-precision rational
  observer; calibration cases returned the arrived point exactly. The grain-43 cases include
  signed product magnitudes beyond 128 bits with small representable quotients.
- `passive_contact_encloses_query_boxes_and_refuses_unfounded_point_pairs`: all eight corners
  of a three-coordinate interval query were enclosed; a coordinate permutation transported the
  entire result, matched observations preserved the query box, and non-point/over-bound founding
  material refused. This control used a legal three-warp, non-power-of-two launch.

[proved-derived; formal-checked] A direct `lake env lean` check of
`ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean` passed. The new printed theorem
dependencies contain only the standing Lean foundations `propext`, `Classical.choice` and
`Quot.sound`; no new axioms or `sorry` were introduced.

[established-bounded; measured] CUDA PTX compilation, the Rust test build, all 34 HNA library
tests and the terminal-row readback regression passed after the new kernel registration.

```sh
cargo test -p holonic-engine --lib passive_contact -- --ignored --nocapture --test-threads=1
```

## Unclosed live binding

[open] This return does not install the candidate in the HNA operation. The next obligation is
to found the actual source/arrived pair, its common metric chart, and retained local successor
at the continuing native interaction, rather than choosing a desired answer or treating the
joining graph's existence as its learning comparison. The body must preserve and use that
changed transport on later occurrences, with the existing persistence/attribution controls.
Only then can the same public text pipeline measure whether it repairs the observed failure.
Useful complete products, ordinary later correction, the second application and HNP5--HNP7
remain required. This finite kernel and formal return are not substitutes for those products.
