# R3 Core edges: declaration-level extraction audit

Source audit for §0.10 and R3 in
[`THE_REPOSITORY_RESTRUCTURE.md`](../THE_REPOSITORY_RESTRUCTURE.md). The extraction matrix began
as a proposal; individual rows now record measured R3 cuts below. Current paths and declaration
namespaces are factual until their corresponding moves land. The initial census itself had no
Lake build; measured R3 cuts and their focused checks are recorded below.

## Transitive paths and cuts from `Framework.Core`

The import graph was traversed from `Framework/Core.lean`, following source `import` lines. The
listed Millennium modules are not direct imports of `Framework.Core`; the receiver row records an
edge that R3 has now removed:

| Millennium module | Core path(s) | Immediate Foundation consumer |
|---|---|---|
<<<<<<< HEAD
| `Gluing` | The generic `GluingPassage` family now lives at `Foundation.GluingPassage`, imported directly by `Foundation.ContinuingTower`. `Framework.Core` no longer reaches `Millennium.Receiver` or `Millennium.Coupling` through JointReceiverDescent after the receiver cut. It still reaches `Millennium.Gluing` through `Foundation.ContinuingTower → Millennium.HolonicDirectedPassage → Millennium.HolonicDifferenceCalculus → Millennium.Swing`; direct research importers remain. | `Foundation.ContinuingTower` uses the new generic owner; research importers continue to use additive and named research declarations. The former `Framework.Core → CausalRelevance → JointReceiverDescent → Millennium.Receiver → Millennium.Coupling → Millennium.Gluing` path is removed. A separate remaining path reaches `Gluing` through `ContinuingTower → HolonicDirectedPassage → HolonicDifferenceCalculus → Swing`. |
| `HolonicDirectedPassage` | `Framework.Core → Standing → RelationLadder → ContinuingTower → HolonicDirectedPassage` | `Foundation.ContinuingTower` uses the successor-witness construction and loop witness. |
| `Receiver` | `Millennium.Receiver` is no longer reachable from `Framework.Core`; Core reaches the already-existing `Foundation.Receiver` through `Standing → RelationLadder → ChangingReceiver → ReceiverHistoryCompression → Lineage → Receiver`. Its generic additive-family declarations also now supply `JointReceiverDescent` directly. | `Foundation.JointReceiverDescent` imports `Foundation.Receiver`; `Millennium.Receiver` imports that owner for its retained chain/theta instance. |
=======
| `Gluing` | The generic `GluingPassage` family now lives at `Foundation.GluingPassage`, imported directly by `Foundation.ContinuingTower`. `Framework.Core` still transitively reaches `Millennium.Gluing` through `Foundation.JointReceiverDescent → Millennium.Receiver → Millennium.Coupling`; other research paths include `Receiver → Theta → Paying/Swing` and direct research importers. | `Foundation.ContinuingTower` uses the new generic owner; research importers continue to use additive and named research declarations. The Core-to-`Receiver` path remains for the distinct Receiver R3 cut. |
| `HolonicDirectedPassage` | **No longer reachable from `Framework.Core` after the directed-passage extraction.** `Transport.WorldTube` and `Framework.Dynamics` still import it outside the Core closure. | `Foundation.ContinuingTower` now imports `Foundation.SuccessorWitnessSystem`; `Transport.WorldTube` retains the research import for `AddressedPassage`. |
| `Receiver` | `Framework.Core → CausalRelevance → JointReceiverDescent → Receiver` | `Foundation.JointReceiverDescent` uses the additive receiver-family kernel. |
>>>>>>> f7e49f5f (Extract coherent successor passage into Lean foundation)
| `ReceiverHistory` (moved) | `Framework.Core → Foundation.CausalRelevance → Foundation.CompleteReceiverHistory`; `Framework.Information` also imports `Foundation.CompleteReceiverHistory` in the full Framework | `Foundation.CausalRelevance` uses the complete receiver-history quotient; Framework, computation, package-root and research callers now import the Foundation owner. |
| `Separation` | `Framework.Core → CausalRelevance → Separation` | `Foundation.CausalRelevance`'s nonlinear section uses `ReceiverFamily` and `collapseOf`. |

After extraction, the remaining direct imports of `HolonicDirectedPassage` are
`Transport.WorldTube`, `Framework.Dynamics`, and its two named research consumers; see the
affected-importer table below. These do not lie on the Core path.

## Extraction matrix

“Generic” here means used as a reusable carrier/operator by Foundation or Framework, not that the
result is mathematically trivial. Extract only these declarations and their minimal imports into
`Holonics`; retain research-specific statements in `HolonicsResearch`. The final target module
names are suggestions and can be resolved when R3 defines the `Holonics` tree.

| Current file and declaration boundary | Generic extraction for `Holonics` | Research-only declarations that remain | Status / uncertainty |
|---|---|---|---|
| [`Millennium/Gluing.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Gluing.lean), 217 lines at census | Lines 32–83: `GluingPassage`; its `Carried`, `Obstruction`, and `Glues`; `carried_is_admissible`; `glues_iff_obstruction_isEmpty`; `not_glues_iff_obstruction_nonempty`. These retain their `Soma.Holonics.Millennium` names and now live in [`Foundation/GluingPassage.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/GluingPassage.lean). `ContinuingTower` imports that owner directly. | `AdditivePassage` and its obstruction/subgroup statements (`glues_iff_obstruction_subsingleton`, `ReachedOnlyInMultiple`, torsion result); `PayingPairing`, `separates`, `no_object_is_invisible` remain in Millennium research with their existing consumers. | **Generic cut landed in `codex/restructure-r3-gluing`;** minimal imports and Lean builds are recorded in `docs/VERIFICATION_RECEIPTS.tsv`. The five-module edge audit remains open; this is not a completed R3. |
<<<<<<< HEAD
| [`Millennium/HolonicDirectedPassage.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicDirectedPassage.lean#L260), 399 lines | `SuccessorWitnessSystem`, `SuccessorWitnessSystem.CoherentSection`, `coherentWitness`, `coherentWitness_compatible`, `coherentSection`, `nonempty_coherentSection` (lines 260–307). These are used by `ContinuingTower.compatible_of_adjacent` and `nonempty_compatibleSection_of_surjectiveAdjacent`. Candidate owner: the generic continuing-tower/foundation owner. | `AddressedCurrent`, `compositionDefect`, `pathCurrent`/`pathDefect` and their finite/closed-path laws; `ComposesExactly`; `HasNullCurrentAlong` and its Cauchy/limit/unique-return laws; reindex/map/pair results. Preserve as a research construction, even if one or more are later consumed by generic tube work. | **Generic cut clear, dependency minimization needed.** The current file imports `HolonicDifferenceCalculus` and `CompleteSeparated` for the larger subject. The successor-system span should be compiled with only its actual dependencies. The Boolean flip loop witness at lines 310–330 is used by ContinuingTower and ContinuingTube as an example; whether it remains as a generic witness or is replaced locally is **unresolved**. |
| [`Millennium/Receiver.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Receiver.lean) | `Foundation/Receiver.lean` owns `collapsedPopulation`, `jointReading`, `jointReading_apply`, `theCollapsedIsTheJointKernel`, and `unseparatedIffDifferenceCollapsed`, retaining their historical declaration namespace through M2. `JointReceiverDescent` imports the foundation owner directly and names `Mathlib.GroupTheory.QuotientGroup.Basic` for its quotient operations. | `receiverChain`, its placement/gluing statements, and the theta-complex instances: cycle/kernel/radical/retained-population equalities, surviving-loop witness, remainder distinction, and theta/hollow-perp comparisons. The research module imports the foundation owner and retains its `Coupling`, `Theta`, and `Triangle` dependencies. | **Source cut and checks complete.** The extracted declarations require only additive groups and the subgroup/kernel API; no research-only hypothesis crosses into Foundation. The consumer imports the quotient-group API directly instead of receiving it accidentally through `Millennium.Coupling`. `Foundation.CausalRelevance` also imports `Mathlib.Algebra.Order.Field.Rat` directly for its rational nonlinear control, formerly supplied transitively through the removed Coupling edge. The focused owner/research build passes at 3,139 jobs, `Framework.Core` at 8,738, and `ElementaryHolonics` at 10,105; all five extracted declarations use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). |
=======
| [`Foundation/SuccessorWitnessSystem.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/SuccessorWitnessSystem.lean), 97 lines | `SuccessorWitnessSystem`, `SuccessorWitnessSystem.CoherentSection`, `coherentWitness`, `coherentWitness_compatible`, `coherentSection`, `nonempty_coherentSection` (original source lines 260–307). These are used by `ContinuingTower.compatible_of_adjacent` and `nonempty_compatibleSection_of_surjectiveAdjacent`. Landed generic owner: `Foundation/SuccessorWitnessSystem.lean`. | `AddressedCurrent`, `compositionDefect`, `pathCurrent`/`pathDefect` and their finite/closed-path laws; `ComposesExactly`; `HasNullCurrentAlong` and its Cauchy/limit/unique-return laws; reindex/map/pair results. Preserve as a research construction, even if one or more are later consumed by generic tube work. | **Generic cut landed in the R3 directed-passage slice.** The new owner imports only `Mathlib.Data.Nat.Basic` and `Mathlib.Logic.IsEmpty.Basic`. The Boolean flip loop witness moved with the generic owner because ContinuingTower and ContinuingTube both cite it. `nonempty_coherentSection` depends only on `Classical.choice`; `boolFlipCoherent_isEmpty` depends only on `propext`. |
| [`Millennium/Receiver.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Receiver.lean#L33), 235 lines | `collapsedPopulation`, `jointReading`, `jointReading_apply`, `theCollapsedIsTheJointKernel`, `unseparatedIffDifferenceCollapsed` (lines 33–62). `JointReceiverDescent` uses `collapsedPopulation`, `jointReading`, and the difference/kernel equivalence. Candidate owner: `Holonics.Receiver`. | `receiverChain`, its placement/gluing statements, and the theta-complex instances: cycle/kernel/radical/retained-population equalities, surviving-loop witness, remainder distinction, and theta/hollow-perp comparisons (from line 64 onward). Their mathematical instance and hypotheses must remain, not migrate to Core. | **Generic cut clear.** The present file imports `Coupling`, `Theta`, and `Triangle` for its research examples; the extracted prefix should not inherit those imports. |
>>>>>>> f7e49f5f (Extract coherent successor passage into Lean foundation)
| [`Foundation/CompleteReceiverHistory.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/CompleteReceiverHistory.lean#L22), 89-line family (historical source path: `ElementaryHolonics/Millennium/ReceiverHistory.lean`) | The generic declaration family used by Foundation: `CompleteReceiverHistoryQuotient`; `causalSignature`; `quotientEq_iff_causalSignatureEq`; `quotientNe_returnsSeparatingReceiverHistory`; `quotientEqualityRetainsBothOccurrences`. The declaration namespace remains `Soma.Holonics.Millennium.ReceiverHistory`; the module now imports `Foundation.ReceiverHistoryCompression` directly. | No distinct Millennium-specific instance theorem was in the former module; the actual research applications remain in their callers. | **Moved in R3 worktree.** Do not conflate this complete-quotient family with the separate `Foundation.ReceiverHistoryCompression` owner. |
| [`Millennium/Separation.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Separation.lean#L149), 496 lines | `ReceiverFamily` and `collapseOf` are now owned by [`Foundation/ReceiverFamily.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverFamily.lean), imported directly by `Foundation.CausalRelevance`; the existing `Soma.Holonics.Millennium.Separation` declaration namespace is retained. No generic lemma is needed by `CausalRelevance.NonLinear`. | Retain polynomial `collapsedPopulation`, separability/coprimality and degree theorems; the Vandermonde blade/discriminant and permutation-hand result; the receiver-family adjunction/separator/readability/cut-separation results; Galois polarity and analysis/modulus examples. These are distinct results or research examples, not needed by Core's current use. | **This extraction is implemented in the R3 separation cut.** `LocalFrame`'s qualified `Separation.collapseOf` is available transitively through `Pivots → MillenniumCoupling → Separation`; `RealizationCorollaries` reaches it through `LocalFrame`. Keep these research paths intact. The remaining research imports include direct users `RH.Xi`, `Millennium.Aperture`, `SeventeenSeparator`, `NavierStokesDirection`, `PrimeAxes`, and `MillenniumCoupling`; preserve their distinct research owners. |

## Source importers to retarget

This records the source-import set found before extraction by exact `import ElementaryHolonics.Millennium.<name>`
search; the `ReceiverHistory` row is historical. It is not a claim that every listed importer consumes the generic declaration.

| Current import | Source importers | Action in R3 |
|---|---|---|
| `Gluing` | `Foundation/ContinuingTower.lean`, `Millennium/{Paying,HolonicUnknotting,Lines,Coupling,Rebase,Swing}.lean` | Foundation imports the extracted owner; research modules split imports if they consume both generic gluing and research declarations. |
<<<<<<< HEAD
| `HolonicDirectedPassage` | `Foundation/ContinuingTower.lean`, `Framework/Dynamics.lean`, `Transport/WorldTube.lean`, `Millennium/{HolonicTerminalCurrent,HolonicSnellInteraction}.lean` | ContinuingTower imports the extracted successor law; other importers are declaration-use dependent and must be audited before removing the old research import. |
| `Receiver` | `Foundation/JointReceiverDescent.lean` imports `Foundation.Receiver` and `Mathlib.GroupTheory.QuotientGroup.Basic`; `Millennium/Receiver.lean` imports the Foundation owner and its research dependencies. | The only direct import was retargeted. Research declarations and their chain/theta dependencies remain in `Millennium.Receiver`. |
=======
| `HolonicDirectedPassage` | `Framework/Dynamics.lean`, `Transport/WorldTube.lean`, `Millennium/{HolonicTerminalCurrent,HolonicSnellInteraction}.lean` | ContinuingTower imports the extracted successor law. WorldTube retains the research import for `AddressedPassage`; Dynamics retains its subject-facade import. |
| `Receiver` | `Foundation/JointReceiverDescent.lean` | Switch to generic receiver owner; retain research import where a consumer still needs `TransportChain` or theta examples. |
>>>>>>> f7e49f5f (Extract coherent successor passage into Lean foundation)
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
4. Keep research imports only where audited declarations require them. `LocalFrame` and
   `RealizationCorollaries` receive `Separation.collapseOf` through the documented
   `Pivots → MillenniumCoupling → Separation` chain. The Boolean-flip witness is generic Foundation
   material; WorldTube keeps the addressed-passage owner for `AddressedPassage`.
5. The R3 statement in §4 calls for building `ElementaryHolonics.Framework` and affected
   research modules. Each measured cut appends its actual source, root, job count, and theorem
   axiom returns below.


## Directed-passage extraction return

The R3 directed-passage cut moves the successor/coherent-section carrier and its sequential
existence theorem to `Foundation/SuccessorWitnessSystem.lean`. It also moves the two-state flip
loop counterexample, because `Foundation/ContinuingTower` and `Transport/ContinuingTube` both cite
it. The exact namespace remains `Soma.Holonics.Millennium.HolonicDirectedPassage` pending M2. The
new owner imports only `Mathlib.Data.Nat.Basic` and `Mathlib.Logic.IsEmpty.Basic`; the successor
law has no hidden directed-current hypotheses. `Millennium/HolonicDirectedPassage` remains the
owner of addressed currents, defects, finite path laws, and null-current/limit results.

`Foundation/ContinuingTower` now imports the new Foundation owner directly, removing that
Foundation-to-research edge. `Transport/WorldTube` continues to import the research module because
it consumes `AddressedPassage`; `Framework.Dynamics` remains a broader subject facade and retains
its direct import. A source import traversal confirms there is no remaining `Millennium` or `RH`
path from `Framework.Core` through `HolonicDirectedPassage`. The other Core research paths through
`Millennium.Receiver` remain and require their own measured cuts. The cached serial verification
passed: the new owner (130 jobs), ContinuingTower (8,715), retained directed-current research
(3,066), WorldTube (3,156), ContinuingTube (8,732), Framework.Dynamics (8,965), Framework.Core
(8,739), and full `ElementaryHolonics` root (10,106). The owner audits the successor theorem at
`Classical.choice` and the Boolean loop witness at `propext`; see the receipt in
`docs/VERIFICATION_RECEIPTS.tsv`.
