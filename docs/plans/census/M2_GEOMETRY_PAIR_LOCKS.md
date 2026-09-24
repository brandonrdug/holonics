# M2 pair-lock owner cut

This bounded cut follows the verified Geometry carry curation at `765123cd`. Focused Lake verification passed; the completed gates and limits are recorded below.

## Declaration ownership

`lock_iff_zero_power` and `lock_is_a_line` moved from
`Geometry/PairResonance.lean` into the pair-contact namespace in
`Transport/HelicalPairInteraction.lean`. The former specializes
`pair_face_power_eq_zero_iff` to rational rates; the latter states scalar closure of a zero-power
rate under the quadratic pair face. They use the pair slip map from HelicalPairInteraction and
`quad`/`faceForm` from its HolonicInteraction dependency. The geometry module no longer imports or
opens HelicalPairInteraction or ScrewGeometry. It retains the mediant, determinant, unimodular
rechart, and coprime-torus laws.

There were no source callers of either declaration outside their original definitions. Their
qualified names now reside under `Soma.Holonics.Transport.HelicalPairInteraction`; no compatibility
alias or duplicate theorem remains. This is a source-ownership move only: no hypotheses, conclusions,
or proofs changed. `Millennium/Farey` and all research theorem owners remain untouched.

Direct source importers on this stack:

| Owner | Direct importers after this cut |
|---|---|
| `Geometry.PairResonance` | `Framework.Geometry` and the `ElementaryHolonics` umbrella |
| `Transport.HelicalPairInteraction` | `Framework.Objects`, `Framework.Dynamics`, `Transport.GeneratorTraceFaces`, `RH.ZeroPairLock`, and the `ElementaryHolonics` umbrella |

## Source import closure

Counts follow project `import ElementaryHolonics.*` lines, include the root itself, and exclude
Mathlib and Lake jobs. The before graph is the verified geometry-carry stack at `765123cd`; after
reflects this cut.

| Source root | Before modules / lines / Millennium | After modules / lines / Millennium | Effect |
|---|---:|---:|---|
| `Geometry.PairResonance` | 15 / 3,399 / 7 | 1 / 92 / 0 | Removes HelicalPairInteraction and its local dependency closure. |
| `Framework.Geometry` | 59 / 16,524 / 15 | 51 / 14,127 / 10 | Eight local modules and five Millennium modules leave this facade's closure. |
| `Framework` | 474 / 172,466 / 277 | 474 / 172,461 / 277 | No module delta: other facade branches already reach Helical's local and research dependencies. |
| `ElementaryHolonics` umbrella | 1,390 / 485,122 / 987 | 1,390 / 485,117 / 987 | No module delta: HelicalPairInteraction is imported directly; only this source's five-line net reduction remains. |

These are source graph counts, not Lake jobs. `Framework.Geometry` retains separate research
imports, including `Millennium.HolonicComposition` and `Millennium.Rigidity`; this cut does not
make that facade research-free. The broad umbrella still imports HelicalPairInteraction directly.

## Focused Lake gates (verified)

Run from `formal/elementary-holonics`:

```sh
lake build ElementaryHolonics.Transport.HelicalPairInteraction
lake build ElementaryHolonics.Geometry.PairResonance
lake build ElementaryHolonics.Transport.GeneratorTraceFaces
lake build ElementaryHolonics.RH.ZeroPairLock
lake build ElementaryHolonics.Framework.Objects
lake build ElementaryHolonics.Framework.Dynamics
lake build ElementaryHolonics.Framework.Geometry
lake build ElementaryHolonics.Framework
```

The first two owners, GeneratorTraceFaces, ZeroPairLock, the Objects/Dynamics/Geometry facades,
and the combined Framework built successfully; the final Framework gate completed 9,197 jobs.
The affected logs contain no error, declaration using `sorry`, or `sorryAx`. Existing linter
suggestions in imported research modules retain their earlier scope. The broad
`ElementaryHolonics` umbrella was built on the immediately preceding geometry-carry cut; it was
not rerun here because this cut changed no umbrella import and all direct theorem consumers plus
the combined Framework built. The eventual `Holonics`/`HolonicsResearch` roots remain unbuilt.
Commands and logs are pinned in `docs/VERIFICATION_RECEIPTS.tsv`.
