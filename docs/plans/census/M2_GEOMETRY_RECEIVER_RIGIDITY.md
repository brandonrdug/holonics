# M2 Receiver shared-junction extraction

This bounded cut follows verified pair-lock curation at `eb0f76b7`. Focused Lake verification passed; the completed gates and limits are recorded below.

## Declaration ownership

The generic `SharedJunction` section's three results moved from
`Millennium/Rigidity.lean` into the core namespace
`Soma.Holonics.Foundation.Receiver` in `Foundation/Receiver.lean`:

- `theSharedJunctionFibreIsTheIntersection`
- `removingTheSecondConstraintCanOnlyEnlargeTheFibre`
- `aContinuationSeenOnlyByTheSecondConstraintIsASeparator`

The owner already formalizes receiver equivalence, compression, and receiver insufficiency. The
shared-junction statements give the exact joint kernel and its separating witness in that same
receiver vocabulary. They are actual moved declarations: the old `Soma.Holonics.Millennium.Rigidity`
names were removed, with no compatibility aliases or duplicate proofs. No external source callers
of these declarations existed.

`Millennium/Rigidity.lean` keeps its concrete exact stress examples: the square with both diagonals,
the collinear triangle, the stress forms, gauge loads, and flex witnesses. Its only direct importer
after the cut is the `ElementaryHolonics` umbrella. `Framework/Geometry.lean` explicitly imports
`Foundation/Receiver` and no longer imports `Millennium/Rigidity`; the owner was already reachable
there through `Framework.Core → Foundation.CausalNaturalHolon → Foundation.Receiver`.

## Source import closure

Counts follow project `import ElementaryHolonics.*` lines, include the root itself, and exclude
Mathlib and Lake jobs. The before graph is verified source at `eb0f76b7`; after reflects this cut.

| Source root | Before modules / lines / Millennium | After modules / lines / Millennium | Effect |
|---|---:|---:|---|
| `Framework.Geometry` | 51 / 14,127 / 10 | 50 / 13,882 / 9 | Removes the concrete Research module; the generic Receiver owner was already in this closure. |
| `Framework` | 474 / 172,461 / 277 | 473 / 172,216 / 276 | Same single-module and one-Millennium reduction. |
| `ElementaryHolonics` umbrella | 1,390 / 485,117 / 987 | 1,390 / 485,119 / 987 | The umbrella retains both modules; the moved section adds two net source lines across its existing closure. |

These are source graph counts, not Lake jobs. `Framework.Geometry` still reaches nine other
Millennium modules, including `Millennium.HolonicComposition`; its generic composition operations
remain pending a separate declaration-owner audit.

## Direct importers

The existing direct importers of `Foundation.Receiver` remain, with `Framework.Geometry` added:
`Algorithm.Transition`, `Computation.{HolonicConstitutiveFibre,JointReceiverWitness,SituatedMachineLearning}`,
`ElementaryHolonics`, `Foundation.{CausalNaturalHolon,ContinuingTower,HigherDifferenceTransport,JointReceiverDescent,Lineage,Presentation,ReceiverRelease,TransportLift}`,
`Framework.Geometry`, `Millennium.{PhysicalRealization,Receiver}`, and
`Transport.ReceiverPotential`. `Millennium.Rigidity` now has one direct importer:
`ElementaryHolonics`.

## Focused Lake gates (verified)

Run from `formal/elementary-holonics`:

```sh
lake build ElementaryHolonics.Foundation.Receiver
lake build ElementaryHolonics.Millennium.Rigidity
lake build ElementaryHolonics.Framework.Geometry
lake build ElementaryHolonics.Framework
```

The moved Receiver owner and retained Rigidity research owner built. The extraction exposed its
actual Mathlib kernel-product owner; `Foundation.Receiver` now imports
`Mathlib.LinearAlgebra.Prod` directly. `Framework.Geometry` and combined `Framework` also built;
the final Framework gate completed 9,196 jobs. Final affected logs have no error, declaration
using `sorry`, `sorryAx`, or linter warning in the changed Receiver owner. The broad umbrella was
verified on the preceding pair-lock source and was not rerun here: its imports are unchanged,
while both direct owners and combined Framework built. The eventual `Holonics` and
`HolonicsResearch` roots remain unbuilt. Commands and logs are pinned in
`docs/VERIFICATION_RECEIPTS.tsv`.
