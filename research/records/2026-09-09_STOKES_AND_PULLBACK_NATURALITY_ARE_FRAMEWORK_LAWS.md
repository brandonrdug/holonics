# Stokes and pullback naturality are framework laws

[project-postulate] Brandon identifies generalized Stokes, the coordinate exterior derivative
and the commuting pullback square as fundamental and possibly underexpressed. This return makes
them an explicit organizing relation in README, canon and the framework guide. It continues the
framework refinement; it does not change the active Athena implementation or its construction order.

## The relation

[proved-standard] For the appropriately oriented smooth domain and form,
`integral_Ω dω = integral_(∂Ω) ω`. In a coordinate coframe,
`dω = sum_i dq^i ∧ partial_i ω`. Smooth pullback satisfies `d f* = f* d`.
These connect local differentiation, oriented integration and compatible chart transport.
The regularity, degree and boundary orientation are part of the statements. References:
[Stokes with corners](https://math.stanford.edu/~conrad/diffgeomPage/handouts/stokescorners.pdf),
[coordinate-free exterior derivative](https://math.stanford.edu/~conrad/diffgeomPage/handouts/dmap.pdf),
and [Mathlib's checked pullback theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html#extDeriv_pullback).

[definition] In the discrete chart, chains carry the oriented incidence and cochains read them.
The existing `LinearMap.dualMap` supplies both the coboundary and the pullback. If
`∂_N F_(k+1)=F_k ∂_M`, the induced pullbacks commute with the cochain differential. When a
proposed transport fails that chain-map square, the exact observed discrepancy is

```text
⟨d_M F_k*ω - F_(k+1)* d_Nω, c⟩
    = ⟨ω, (F_k ∂_M - ∂_N F_(k+1)) c⟩.
```

[proved-derived; formal-checked] New `Geometry/ExteriorBoundary.lean` proves `stokes_pairing`,
`coboundary_squared`, `pullback_coboundary` and `pullback_coboundary_defect` over the existing
linear-dual owner. Its source types can be adjacent chain grades; no new complex or execution
engine is founded. The Geometry framework import exposes it together with Mathlib's actual
smooth normed-space `extDeriv_pullback`, `extDerivWithin_pullback` and `extDeriv_extDeriv`.
This does not assert a newly implemented global manifold integration theorem.

## Recovered owners and repaired scope

[established-bounded; source-inspected] At `ca5dba5b`, the framework already included the triangle
pairing `Polarisation.theAdjointnessIsStokes`, its `HolonicDifferenceCalculus` consumer, addressed
boundary cancellation, four-torus chain boundaries and cuts, smooth pressure exact forms and
six-face flux integration. Stokes was already a sentence in `02_INFORMATION_PHYSICS.md`.
The main presentation did not expose their common exterior/pullback relation.

[definition] `Polarisation.lean`'s prose now matches its declarations. Equal boundary/interior
pairings retain the unobserved source fibre; they do not establish complete reconstruction.
The triangle calculation supplies its boundary cancellation, not a full proof of smooth Stokes
from `∂²=0`. Its sign-flip fixed-point lemma is algebra over rational triples, not a construction
or classification of a Möbius band. Nonorientability obstructs global ordinary orientation while
leaving local and appropriately twisted/density formulations available. Gauss–Bonnet retains
its additional curvature and global topology. No existing theorem or namespace was removed.

## Consequence for construction

[project-postulate] Treat differentiation, boundary reading and transport as one compatible
diagram when the construction claims that structure. A coarse receiver preserving today's value
does not automatically preserve the differential; the complete signed defect identifies the
remaining relation. This strengthens the existing boundary-scale and future-receiver discipline.

[definition] Ordinary d is metric-independent; material laws, Hodge operators and Hilbert adjoints
add their actual metric and constitutive data. In moving coframes, dθ terms survive. For a bundle
connection, covariant exterior differentiation carries curvature, while ordinary d has square
zero. Closed forms need not be globally exact. These distinctions preserve the active interior,
the torus winding classes and the geometric content of twisting, rather than reducing them to
one scalar boundary measurement.

[conditional] With a realized space-time current J and source law dJ=S, the same theorem on a
world-tube equates final-minus-initial stored quantity plus outward lateral flux to integrated
source. Temporal storage and spatial transport are boundary faces of one region; their actual
units, source law and constitutive attachment remain part of the physical realization.

[established-bounded; process-audit] The focused exterior-boundary target passed (2,114 jobs).
The complete framework and existing `HolonicDifferenceCalculus` consumer passed (4,002 jobs),
including the unchanged declarations of the prose-corrected triangle owner. The new axiom audit
contains only `propext`, `Classical.choice` and `Quot.sound`. No native kernel or Athena state
was changed, and no new physical or global reconstruction claim was inferred from the pairing.
