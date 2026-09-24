# M2 addressed linearized passage cut

This declaration-level cut is based on the stacked M1 causal-chord source. It separates a reusable
linearized transport law from the situated returned-difference Research owner; it does not create
the new `Holonics` or `HolonicsResearch` Lake roots and does not claim Lake verification.

## Ownership and import changes

`Transport/AddressedLinearizedPassage.lean` now owns `AddressedLinearizedPassage`,
`AddressedTwoStepWord`, the two-step differential and reverse adjoint, and the corresponding
receiver-radical and full-preimage-fibre laws. The declaration namespace is
`Soma.Holonics.Transport.AddressedLinearizedPassage`. Its source imports are `Foundation.Lineage`
and the Mathlib adjoint/finite-dimensional APIs. The addressed occurrence join remains an explicit
operand; no inverse or injectivity assumption is introduced.

`Computation/HolonicAdjointNormalization.lean` had been the only external source importer of the
old addressed-adjoint declarations. Its `causalAdjoint_returns_in_reverse_factor_order` theorem
only restated the moved adjoint theorem, so the wrapper, its import/open, and its axiom audit line
were removed. `Framework.Dynamics` now imports the new owner as part of its public subject surface.
The source search found no other consumer of the wrapper or moved names outside their original
owner and that computation module.

`Millennium/SituatedReturnedDifference.lean` retains
`DependentAdditiveConnectionSquare`, `dependentReturnedDifference`, and
`dependentReturnedDifference_rebase`. The moved addressed-adjoint section and its three audit lines
were removed. `Transport/WorldTube` and `Computation/SituatedMachineLearning` still import the
Research module for other declarations; those edges are not part of this cut.

## Source import closure

Counts below follow only project `import ElementaryHolonics.*` lines, including the root itself;
they exclude Mathlib modules and Lake jobs. “Before” substitutes the pre-cut
`HolonicAdjointNormalization → Millennium.SituatedReturnedDifference` edge into the current graph;
the current graph also includes the new `Framework.Dynamics → Transport.AddressedLinearizedPassage`
edge.

| Source root | Before modules / Millennium or RH | After modules / Millennium or RH | Effect |
|---|---:|---:|---|
| `Computation.HolonicAdjointNormalization` | 6 / 1 | 3 / 0 | Removes the Research module and the redundant causal wrapper and its dependencies from the generic normalization owner. |
| `Objects.Ratio` | 16 / 2 | 14 / 1 | Removes `Millennium.SituatedReturnedDifference`; `Millennium.Turn` remains through the independent winding proofs. |
| `Framework.Information` | 155 / 107 | 154 / 106 | Removes the `SituatedReturnedDifference` Research edge; its other theorem-source imports remain. |
| `Framework.Objects` | 110 / 24 | 110 / 24 | No Millennium-count change: `Transport.WorldTube` independently reaches the retained Research module. |
| `Framework.Dynamics` | 89 / 21 | 90 / 21 | Adds the new public Transport owner; its existing research edges are unchanged. |

This is import-graph evidence, not a successful Lean check. Exact focused build commands for the
first verification pass are:

```sh
cd formal/elementary-holonics
lake build ElementaryHolonics.Transport.AddressedLinearizedPassage \
  ElementaryHolonics.Computation.HolonicAdjointNormalization \
  ElementaryHolonics.Millennium.SituatedReturnedDifference \
  ElementaryHolonics.Objects.Ratio \
  ElementaryHolonics.Objects.RatioPhase \
  ElementaryHolonics.Objects.RatioBlock \
  ElementaryHolonics.Framework.Objects \
  ElementaryHolonics.Framework.Information \
  ElementaryHolonics.Framework.Dynamics
```

The eventual M2 acceptance gates remain `lake build Holonics` and `lake build HolonicsResearch`
after those roots and the remaining declaration cuts exist.
