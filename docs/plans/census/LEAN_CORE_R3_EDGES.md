# R3 Core edges: declaration-level extraction audit

Source audit for §0.10 and R3 in
[`THE_REPOSITORY_RESTRUCTURE.md`](../THE_REPOSITORY_RESTRUCTURE.md). The extraction matrix began
as a proposal; individual rows now record measured R3 cuts below. Current paths and declaration
namespaces are factual until their corresponding moves land. The initial census itself had no
Lake build; measured R3 cuts and their focused checks are recorded below.

## Transitive paths and cuts from `Framework.Core`

The import graph was traversed from `Framework/Core.lean`, following source `import` lines. The
listed Millennium modules were not direct imports of `Framework.Core`. The rows now record
their extracted generic owners and remaining research-only import paths:

| Millennium module | Core path(s) | Immediate Foundation consumer |
|---|---|---|
| `Gluing` | `Foundation.GluingPassage` now owns the generic carrier. Core no longer reaches mixed `Millennium.Gluing` through `Receiver → Coupling` or `HolonicDirectedPassage → HolonicDifferenceCalculus → Swing`; direct research importers remain. | `Foundation.ContinuingTower` imports the generic owner; research modules retain additive and named gluing results. |
| `HolonicDirectedPassage` | **No longer reachable from `Framework.Core` after the directed-passage extraction.** `Transport.WorldTube` and `Framework.Dynamics` still import it outside the Core closure. | `Foundation.ContinuingTower` now imports `Foundation.SuccessorWitnessSystem`; `Transport.WorldTube` retains the research import for `AddressedPassage`. |
| `Receiver` | `Millennium.Receiver` is no longer reachable from `Framework.Core`; Core reaches the already-existing `Foundation.Receiver` through `Standing → RelationLadder → ChangingReceiver → ReceiverHistoryCompression → Lineage → Receiver`. Its generic additive-family declarations also now supply `JointReceiverDescent` directly. | `Foundation.JointReceiverDescent` imports `Foundation.Receiver`; `Millennium.Receiver` imports that owner for its retained chain/theta instance. |
| `ReceiverHistory` (moved) | `Framework.Core → Foundation.CausalRelevance → Foundation.CompleteReceiverHistory`; `Framework.Information` also imports `Foundation.CompleteReceiverHistory` in the full Framework | `Foundation.CausalRelevance` uses the complete receiver-history quotient; Framework, computation, package-root and research callers now import the Foundation owner. |
| `Separation` | No longer reachable through `Foundation.CausalRelevance`; that owner now imports `Foundation.ReceiverFamily` for `ReceiverFamily` and `collapseOf`. Research importers still use the mixed `Millennium.Separation` file. | The nonlinear Core section uses the generic collapse relation without the polynomial, Galois or analysis results. |

After extraction, the remaining direct imports of `HolonicDirectedPassage` are
`Transport.WorldTube`, `Framework.Dynamics`, and its two named research consumers; see the
affected-importer table below. These do not lie on the Core path.
A recursive traversal of current `import ElementaryHolonics.*` source lines from
`Framework.Core` reaches 26 in-package modules with no missing source and zero `Millennium` or
`RH` modules after the five generic cuts. This is a source-import count, distinct from Lake's
Mathlib-inclusive build job count; the full `Framework` facade still imports research through
other entries.

## Extraction matrix

“Generic” here means used as a reusable carrier/operator by Foundation or Framework, not that the
result is mathematically trivial. Extract only these declarations and their minimal imports into
`Holonics`; retain research-specific statements in `HolonicsResearch`. The final target module
names are suggestions and can be resolved when R3 defines the `Holonics` tree.

| Current file and declaration boundary | Generic extraction for `Holonics` | Research-only declarations that remain | Status / uncertainty |
|---|---|---|---|
| [`Millennium/Gluing.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Gluing.lean), 217 lines at census | Lines 32–83: `GluingPassage`; its `Carried`, `Obstruction`, and `Glues`; `carried_is_admissible`; `glues_iff_obstruction_isEmpty`; `not_glues_iff_obstruction_nonempty`. These retain their `Soma.Holonics.Millennium` names and now live in [`Foundation/GluingPassage.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/GluingPassage.lean). `ContinuingTower` imports that owner directly. | `AdditivePassage` and its obstruction/subgroup statements (`glues_iff_obstruction_subsingleton`, `ReachedOnlyInMultiple`, torsion result); `PayingPairing`, `separates`, `no_object_is_invisible` remain in Millennium research with their existing consumers. | **Generic cut landed in `codex/restructure-r3-gluing`;** minimal imports and Lean builds are recorded in `docs/VERIFICATION_RECEIPTS.tsv`. The remaining Core path through mixed Gluing was cut by the later Receiver and directed-passage slices; R3 remains open for the Ratio/MomentStorage and full-Framework ingress paths. |
| [`Foundation/SuccessorWitnessSystem.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/SuccessorWitnessSystem.lean), 97 lines | `SuccessorWitnessSystem`, `SuccessorWitnessSystem.CoherentSection`, `coherentWitness`, `coherentWitness_compatible`, `coherentSection`, `nonempty_coherentSection` (original source lines 260–307). These are used by `ContinuingTower.compatible_of_adjacent` and `nonempty_compatibleSection_of_surjectiveAdjacent`. Landed generic owner: `Foundation/SuccessorWitnessSystem.lean`. | `AddressedCurrent`, `compositionDefect`, `pathCurrent`/`pathDefect` and their finite/closed-path laws; `ComposesExactly`; `HasNullCurrentAlong` and its Cauchy/limit/unique-return laws; reindex/map/pair results. Preserve as a research construction, even if one or more are later consumed by generic tube work. | **Generic cut landed in the R3 directed-passage slice.** The new owner imports only `Mathlib.Data.Nat.Basic` and `Mathlib.Logic.IsEmpty.Basic`. The Boolean flip loop witness moved with the generic owner because ContinuingTower and ContinuingTube both cite it. `nonempty_coherentSection` depends only on `Classical.choice`; `boolFlipCoherent_isEmpty` depends only on `propext`. |
| [`Millennium/Receiver.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Receiver.lean) | `Foundation/Receiver.lean` owns `collapsedPopulation`, `jointReading`, `jointReading_apply`, `theCollapsedIsTheJointKernel`, and `unseparatedIffDifferenceCollapsed`, retaining their historical declaration namespace through M2. `JointReceiverDescent` imports the foundation owner directly and names `Mathlib.GroupTheory.QuotientGroup.Basic` for its quotient operations. | `receiverChain`, its placement/gluing statements, and the theta-complex instances: cycle/kernel/radical/retained-population equalities, surviving-loop witness, remainder distinction, and theta/hollow-perp comparisons. The research module imports the foundation owner and retains its `Coupling`, `Theta`, and `Triangle` dependencies. | **Source cut and checks complete.** The extracted declarations require only additive groups and the subgroup/kernel API; no research-only hypothesis crosses into Foundation. The consumer imports the quotient-group API directly instead of receiving it accidentally through `Millennium.Coupling`. `Foundation.CausalRelevance` also imports `Mathlib.Algebra.Order.Field.Rat` directly for its rational nonlinear control, formerly supplied transitively through the removed Coupling edge. The focused owner/research build passes at 3,139 jobs, `Framework.Core` at 8,738, and `ElementaryHolonics` at 10,105; all five extracted declarations use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). |
| [`Foundation/CompleteReceiverHistory.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/CompleteReceiverHistory.lean#L22), 89-line family (historical source path: `ElementaryHolonics/Millennium/ReceiverHistory.lean`) | The generic declaration family used by Foundation: `CompleteReceiverHistoryQuotient`; `causalSignature`; `quotientEq_iff_causalSignatureEq`; `quotientNe_returnsSeparatingReceiverHistory`; `quotientEqualityRetainsBothOccurrences`. The declaration namespace remains `Soma.Holonics.Millennium.ReceiverHistory`; the module now imports `Foundation.ReceiverHistoryCompression` directly. | No distinct Millennium-specific instance theorem was in the former module; the actual research applications remain in their callers. | **Moved in R3 worktree.** Do not conflate this complete-quotient family with the separate `Foundation.ReceiverHistoryCompression` owner. |
| [`Millennium/HolonicConnectionCurvature.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicConnectionCurvature.lean) and [`Millennium/HolonicGaugeCovariance.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicGaugeCovariance.lean) | The Ratio-facing chart, directional derivative, connection carrier and minimal smooth/product rules now live in [`Geometry/ConnectionCalculus.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Geometry/ConnectionCalculus.lean). `Gauge`, `gaugeTransform`, their differentiated inverse/transform laws now live in [`Objects/Ratio/GaugeCalculus.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Objects/Ratio/GaugeCalculus.lean), retaining historical declaration namespaces. `Objects.Ratio` imports the core gauge owner directly. | Curvature, Bianchi, variation, Ricci and `curvature_gaugeTransform` remain in their Millennium sources. `HolonicGaugeCovariance` now imports curvature directly and no longer imports Variation; no forwarding aliases are introduced. | **Source cut landed in `codex/restructure-r3-ratio`; Lake checks pass (focused importers 8,929 jobs; top-level `ElementaryHolonics` 10,107 jobs).** The source graph no longer has the Ratio-to-Variation path. Static source closure falls only from 50,139 to 49,827 lines because `Physics.InformationDifference` independently brings 47,269 lines; the removed edge is not a 45k net reduction. |
| [`Millennium/Separation.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Millennium/Separation.lean#L149), 496 lines | `ReceiverFamily` and `collapseOf` are now owned by [`Foundation/ReceiverFamily.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverFamily.lean), imported directly by `Foundation.CausalRelevance`; the existing `Soma.Holonics.Millennium.Separation` declaration namespace is retained. No generic lemma is needed by `CausalRelevance.NonLinear`. | Retain polynomial `collapsedPopulation`, separability/coprimality and degree theorems; the Vandermonde blade/discriminant and permutation-hand result; the receiver-family adjunction/separator/readability/cut-separation results; Galois polarity and analysis/modulus examples. These are distinct results or research examples, not needed by Core's current use. | **This extraction is implemented in the R3 separation cut.** `LocalFrame`'s qualified `Separation.collapseOf` is available transitively through `Pivots → MillenniumCoupling → Separation`; `RealizationCorollaries` reaches it through `LocalFrame`. Keep these research paths intact. The remaining research imports include direct users `RH.Xi`, `Millennium.Aperture`, `SeventeenSeparator`, `NavierStokesDirection`, `PrimeAxes`, and `MillenniumCoupling`; preserve their distinct research owners. |

## Source importers to retarget

This records the source-import set found before extraction by exact `import ElementaryHolonics.Millennium.<name>`
search; the `ReceiverHistory` row is historical. It is not a claim that every listed importer consumes the generic declaration.

| Current import | Source importers | Action in R3 |
|---|---|---|
| `Gluing` | `Foundation/ContinuingTower.lean`, `Millennium/{Paying,HolonicUnknotting,Lines,Coupling,Rebase,Swing}.lean` | Foundation imports the extracted owner; research modules split imports if they consume both generic gluing and research declarations. |
| `HolonicDirectedPassage` | `Framework/Dynamics.lean`, `Transport/WorldTube.lean`, `Millennium/{HolonicTerminalCurrent,HolonicSnellInteraction}.lean` | ContinuingTower imports the extracted successor law. WorldTube retains the research import for `AddressedPassage`; Dynamics retains its subject-facade import. |
| `Receiver` | `Foundation/JointReceiverDescent.lean` imports `Foundation.Receiver` and `Mathlib.GroupTheory.QuotientGroup.Basic`; `Millennium/Receiver.lean` imports the Foundation owner and its research dependencies. | The only direct import was retargeted. Research declarations and their chain/theta dependencies remain in `Millennium.Receiver`. |
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
path from `Framework.Core` through `HolonicDirectedPassage`. The separate Core path through `Millennium.Receiver` was cut by the stacked Receiver slice;
full Framework research ingress through Ratio and other subject facades remains for later measured cuts. The cached serial verification
passed: the new owner (130 jobs), ContinuingTower (8,715), retained directed-current research
(3,066), WorldTube (3,156), ContinuingTube (8,732), Framework.Dynamics (8,965), Framework.Core
(8,739), and full `ElementaryHolonics` root (10,106). The owner audits the successor theorem at
`Classical.choice` and the Boolean loop witness at `propext`; see the receipt in
`docs/VERIFICATION_RECEIPTS.tsv`.

## Quadratic-moment owner return

`Holon/QuadraticMoment.lean` now owns the finite weighted second moment, bilinear contraction,
support enumeration and their exact equality. `Holon/MomentStorage` and
`Geometry/ScrewGeometry` import this generic owner directly; `Framework/Information` uses it
instead of the research condensation file. The latter retains its distinct equal-moment and
receiver-sufficiency theorems and imports the generic owner. Historical declaration names and
namespace remain stable pending M2. This cut removes a research import from two object owners;
it does not claim that the full Framework is research-free, since other subject facades still
import independent research modules.

On the source cut, focused Lake builds passed for `Holon.MomentStorage` (3,110 jobs),
`Geometry.ScrewGeometry` (3,009), `Framework.Information` (8,860), and the retained research
module (1,226); the full `ElementaryHolonics` root passed (10,106). A source-import traversal
measured the `MomentStorage` closure dropping from 137 modules / 49,263 lines to seven modules /
1,527 lines, and `ScrewGeometry` from 132 / 48,000 to two / 264. The full Framework closure
drops only from 543 / 190,674 to 541 / 189,682 because separate imports still reach research.
