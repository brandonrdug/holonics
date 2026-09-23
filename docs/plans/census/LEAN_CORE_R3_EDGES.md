# R3 Core edges: declaration-level extraction audit

Source audit for §0.10 and R3 in
[`THE_REPOSITORY_RESTRUCTURE.md`](../THE_REPOSITORY_RESTRUCTURE.md). The extraction matrix began
as a proposal; individual rows now record measured R3 cuts below. Current paths and declaration
namespaces are factual until their corresponding moves land. The initial census itself had no
Lake build; the separation cut's checked builds are recorded below.

## The five transitive paths from `Framework.Core`

The import graph was traversed from `Framework/Core.lean`, following source `import` lines. The
five listed Millennium modules are not direct imports of `Framework.Core`:

| Millennium module | Core path(s) | Immediate Foundation consumer |
|---|---|---|
| `Gluing` | `Framework.Core → Foundation.CausalRelevance → Foundation.JointReceiverDescent → Millennium.Receiver → Millennium.Coupling → Millennium.Gluing`; also `… → Receiver → Theta → Paying/Swing → Gluing`; and `Framework.Core → Foundation.Standing → Foundation.RelationLadder → Foundation.ContinuingTower → Gluing` | `Foundation.ContinuingTower` uses `GluingPassage` and its obstruction equivalence. `Receiver` currently has a separate transitive path through research modules. |
| `HolonicDirectedPassage` | `Framework.Core → Standing → RelationLadder → ContinuingTower → HolonicDirectedPassage` | `Foundation.ContinuingTower` uses the successor-witness construction and loop witness. |
| `Receiver` | `Framework.Core → CausalRelevance → JointReceiverDescent → Receiver` | `Foundation.JointReceiverDescent` uses the additive receiver-family kernel. |
| `ReceiverHistory` (moved) | `Framework.Core → Foundation.CausalRelevance → Foundation.CompleteReceiverHistory`; `Framework.Information` also imports `Foundation.CompleteReceiverHistory` in the full Framework | `Foundation.CausalRelevance` uses the complete receiver-history quotient; Framework, computation, package-root and research callers now import the Foundation owner. |
| `Separation` | `Framework.Core → CausalRelevance → Separation` | `Foundation.CausalRelevance`'s nonlinear section uses `ReceiverFamily` and `collapseOf`. |

The direct-import inventory also finds `Transport.WorldTube` and `Framework.Dynamics` importing
`HolonicDirectedPassage`; see the affected-importer table below. These importers are not all on the
Core path, but must be retargeted when the generic declarations move.

## Extraction matrix

“Generic” here means used as a reusable carrier/operator by Foundation or Framework, not that the
result is mathematically trivial. Extract only these declarations and their minimal imports into
`Holonics`; retain research-specific statements in `HolonicsResearch`. The final target module
names are suggestions and can be resolved when R3 defines the `Holonics` tree.

| Current file and declaration boundary | Generic extraction for `Holonics` | Research-only declarations that remain | Status / uncertainty |
|---|---|---|---|
| [`Millennium/Gluing.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Gluing.lean#L32), 217 lines | Lines 32–83: `GluingPassage`; its `Carried`, `Obstruction`, and `Glues`; `carried_is_admissible`; `glues_iff_obstruction_isEmpty`; `not_glues_iff_obstruction_nonempty`. These are the exact names used by `Foundation/ContinuingTower.lean` (`gluingPassage`, `carried_iff_observationFibre`, `obstruction_nonempty_iff`, `shiftTower_not_glues`). Candidate owner: `Holonics.Gluing` or the Holarchy/gluing owner when it lands. | `AdditivePassage` and its obstruction/subgroup statements (`glues_iff_obstruction_subsingleton`, `ReachedOnlyInMultiple`, torsion result); `PayingPairing`, `separates`, `no_object_is_invisible`. Keep with Millennium research consumers; do not import these into Core just to reach `GluingPassage`. | **Generic cut clear.** Verify the extracted header has no dependency on the module's rational-field and quotient-group imports unless required by declarations in the extracted span. |
| [`Millennium/HolonicDirectedPassage.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicDirectedPassage.lean#L260), 399 lines | `SuccessorWitnessSystem`, `SuccessorWitnessSystem.CoherentSection`, `coherentWitness`, `coherentWitness_compatible`, `coherentSection`, `nonempty_coherentSection` (lines 260–307). These are used by `ContinuingTower.compatible_of_adjacent` and `nonempty_compatibleSection_of_surjectiveAdjacent`. Candidate owner: the generic continuing-tower/foundation owner. | `AddressedCurrent`, `compositionDefect`, `pathCurrent`/`pathDefect` and their finite/closed-path laws; `ComposesExactly`; `HasNullCurrentAlong` and its Cauchy/limit/unique-return laws; reindex/map/pair results. Preserve as a research construction, even if one or more are later consumed by generic tube work. | **Generic cut clear, dependency minimization needed.** The current file imports `HolonicDifferenceCalculus` and `CompleteSeparated` for the larger subject. The successor-system span should be compiled with only its actual dependencies. The Boolean flip loop witness at lines 310–330 is used by ContinuingTower and ContinuingTube as an example; whether it remains as a generic witness or is replaced locally is **unresolved**. |
| [`Millennium/Receiver.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Receiver.lean#L33), 235 lines | `collapsedPopulation`, `jointReading`, `jointReading_apply`, `theCollapsedIsTheJointKernel`, `unseparatedIffDifferenceCollapsed` (lines 33–62). `JointReceiverDescent` uses `collapsedPopulation`, `jointReading`, and the difference/kernel equivalence. Candidate owner: `Holonics.Receiver`. | `receiverChain`, its placement/gluing statements, and the theta-complex instances: cycle/kernel/radical/retained-population equalities, surviving-loop witness, remainder distinction, and theta/hollow-perp comparisons (from line 64 onward). Their mathematical instance and hypotheses must remain, not migrate to Core. | **Generic cut clear.** The present file imports `Coupling`, `Theta`, and `Triangle` for its research examples; the extracted prefix should not inherit those imports. |
| [`Foundation/CompleteReceiverHistory.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/CompleteReceiverHistory.lean#L22), 89-line family (historical source path: `ElementaryHolonics/Millennium/ReceiverHistory.lean`) | The generic declaration family used by Foundation: `CompleteReceiverHistoryQuotient`; `causalSignature`; `quotientEq_iff_causalSignatureEq`; `quotientNe_returnsSeparatingReceiverHistory`; `quotientEqualityRetainsBothOccurrences`. The declaration namespace remains `Soma.Holonics.Millennium.ReceiverHistory`; the module now imports `Foundation.ReceiverHistoryCompression` directly. | No distinct Millennium-specific instance theorem was in the former module; the actual research applications remain in their callers. | **Moved in R3 worktree.** Do not conflate this complete-quotient family with the separate `Foundation.ReceiverHistoryCompression` owner. |
| [`Millennium/Separation.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Separation.lean#L149), 496 lines | `ReceiverFamily` and `collapseOf` are now owned by [`Foundation/ReceiverFamily.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverFamily.lean), imported directly by `Foundation.CausalRelevance`; the existing `Soma.Holonics.Millennium.Separation` declaration namespace is retained. No generic lemma is needed by `CausalRelevance.NonLinear`. | Retain polynomial `collapsedPopulation`, separability/coprimality and degree theorems; the Vandermonde blade/discriminant and permutation-hand result; the receiver-family adjunction/separator/readability/cut-separation results; Galois polarity and analysis/modulus examples. These are distinct results or research examples, not needed by Core's current use. | **This extraction is implemented in the R3 separation cut.** `LocalFrame`'s qualified `Separation.collapseOf` is available transitively through `Pivots → MillenniumCoupling → Separation`; `RealizationCorollaries` reaches it through `LocalFrame`. Keep these research paths intact. The remaining research imports include direct users `RH.Xi`, `Millennium.Aperture`, `SeventeenSeparator`, `NavierStokesDirection`, `PrimeAxes`, and `MillenniumCoupling`; preserve their distinct research owners. |

## Source importers to retarget

This records the source-import set found before extraction by exact `import ElementaryHolonics.Millennium.<name>`
search; the `ReceiverHistory` row is historical. It is not a claim that every listed importer consumes the generic declaration.

| Current import | Source importers | Action in R3 |
|---|---|---|
| `Gluing` | `Foundation/ContinuingTower.lean`, `Millennium/{Paying,HolonicUnknotting,Lines,Coupling,Rebase,Swing}.lean` | Foundation imports the extracted owner; research modules split imports if they consume both generic gluing and research declarations. |
| `HolonicDirectedPassage` | `Foundation/ContinuingTower.lean`, `Framework/Dynamics.lean`, `Transport/WorldTube.lean`, `Millennium/{HolonicTerminalCurrent,HolonicSnellInteraction}.lean` | ContinuingTower imports the extracted successor law; other importers are declaration-use dependent and must be audited before removing the old research import. |
| `Receiver` | `Foundation/JointReceiverDescent.lean` | Switch to generic receiver owner; retain research import where a consumer still needs `TransportChain` or theta examples. |
| `ReceiverHistory` (former path) | `ElementaryHolonics.lean`, `Foundation/CausalRelevance.lean`, `Framework/Information.lean`, `Computation/{HolonicExcitationFoundedQuotient,HolonicNeuralEcology}.lean`, `Millennium/{HolonicGranularBoundaryRadiation,HolonicFiniteCausalAperture}.lean` | **Moved:** all seven importers now import `Foundation.CompleteReceiverHistory`; the former `Millennium/ReceiverHistory.lean` source path is retired. |
| `Separation` | `Foundation/CausalRelevance.lean`, `RH/Xi.lean`, `Millennium/{Aperture,MillenniumCoupling,NavierStokesDirection,PrimeAxes,SeventeenSeparator}.lean`; qualified use in `Millennium/LocalFrame.lean` and `RealizationCorollaries.lean` | CausalRelevance now imports `Foundation.ReceiverFamily`; `Separation` itself imports that generic owner and retains its research theorems. `LocalFrame`'s qualified use is supplied by `Pivots → MillenniumCoupling → Separation`; `RealizationCorollaries` receives it through `LocalFrame`. Those are deliberate research dependencies, so keep them. |

## Implemented R3 separation cut (#66)

`Foundation/ReceiverFamily.lean` now owns the two declarations required by the Core consumer,
with only `Mathlib.Data.Set.Defs` imported. The names remain in
`Soma.Holonics.Millennium.Separation` pending M2. `Foundation/CausalRelevance` imports this owner
directly; `Millennium/Separation` imports it before stating the retained research family. There is
no Foundation-to-Millennium import edge introduced by this cut. The source audit found no generic
Separation lemma consumed by `CausalRelevance`.

On September 23, cached Lake verification passed for `Foundation.ReceiverFamily`,
`Foundation.CausalRelevance`, `Millennium.Separation`, and `Framework.Core` (8,744 jobs), then for
the full `ElementaryHolonics.Framework` root plus all listed direct/qualified research consumers
(`RH.Xi`, `Millennium.Aperture`, `MillenniumCoupling`, `NavierStokesDirection`, `PrimeAxes`,
`SeventeenSeparator`, `LocalFrame`, and `RealizationCorollaries`; 9,366 jobs). No Lean law or
research theorem was weakened or removed. Other rows in the extraction matrix remain proposals;
this verification does not complete R3.

## R3 gates and unresolved points

1. Extract each generic declaration together with its actual minimal imports; do not move the five
   mixed modules wholesale into `Holonics`.
2. Update all affected in-repository importers in the same R3 change. Confirm there is no
   `Holonics → HolonicsResearch` dependency, including transitive module imports.
3. Build the new `Framework.Core` closure and the affected modules/importers. Then run the R3 plan's
   broader `ElementaryHolonics.Framework` and affected research-module builds. Record the measured
   new closure and build receipts; no target closure size is inferred from this audit.
4. Audit declaration uses in the research importers before deleting or narrowing old imports.
   In particular, resolve the non-direct `Separation.collapseOf` references and the Boolean-flip
   loop witness before cutting either source owner.
5. The current R3 statement in §4 calls for building `ElementaryHolonics.Framework` and affected
   research modules. No implementation or build is claimed here.
