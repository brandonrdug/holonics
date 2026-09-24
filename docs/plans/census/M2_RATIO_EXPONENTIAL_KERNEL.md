# M2 Ratio exponential-kernel cut

This is the second bounded Ratio cut, stacked on the addressed-linearized-passage cut. It moves
one generic theorem into the public Ratio owner and leaves geometric turn calibration and its
named applications in Research. Focused Lake verification passed; the gates and limits are recorded below.

## Declaration ownership

`Objects/Ratio/ExponentialKernel.lean` now owns
`Soma.Holonics.Objects.Ratio.ExponentialKernel.exp_eq_one_iff_integer_period`, proved directly
by Mathlib's `Complex.exp_eq_one_iff`. `Objects/Ratio.lean` imports this owner, drops its direct
`Millennium.Turn` import, and retargets its three winding proof sites: `amplitude_windShift`,
`amplitude_eq_iff_winding`, and `logFibre_torsor`.

`Millennium/Turn.lean` no longer declares the generic kernel theorem. Its geometric turn
calibration, real-chart results, half-angle results and golden-clock residue remain in Research.
The source search found no caller of the removed declaration outside `Objects/Ratio`. The only
remaining direct importers of `Millennium.Turn` are `Millennium/Coupling`, which uses its named
fifth-turn result, and `Millennium/NavierStokesH2TriadMultiplierSwing`, which uses its calibration
owner. The former direct imports in `Millennium/HolonicPolygonalTorusCarrier` and
`Millennium/HolonicSnellInteraction` had no source use of any `Turn` declaration and were removed.
No compatibility alias or duplicate theorem is kept. The R0 importer census records the earlier
baseline; this current importer list is based on the stacked source.

## Source import closure

Counts follow project `import ElementaryHolonics.*` lines, include the root itself, and exclude
Mathlib and Lake jobs. The pre-cut graph is the immediately preceding addressed-passage stack.

| Source root | Before modules / Millennium | After modules / Millennium | Effect |
|---|---:|---:|---|
| `Objects.Ratio` | 14 / 1 | 14 / 0 | Replaces the `Millennium.Turn` module with the Ratio kernel owner. |
| `Objects.RatioPhase` | 15 / 1 | 15 / 0 | Its dependency on Ratio now has no Turn path. |
| `Objects.RatioBlock` | 15 / 1 | 15 / 0 | Its dependency on Ratio now has no Turn path. |
| `Framework.Objects` | 110 / 24 | 110 / 23 | Its Ratio branch replaces Turn with the core kernel owner; no other Turn path enters this subject closure. |
| `Framework` | 475 / 279 | 476 / 279 | The broader facade still reaches Turn through Coupling; its Millennium count is unchanged. |

The full public root is not expected to import `Millennium.Turn` through the Ratio branch after
this cut; the current subject facade count is not a claim that the final root has been curated.
In particular, the `Framework` and `Framework.Objects` closures include independent research
paths, so their Millennium counts do not measure this isolated import removal.

## Focused Lake gates (verified)

```sh
cd formal/elementary-holonics
lake build ElementaryHolonics.Objects.Ratio.ExponentialKernel \
  ElementaryHolonics.Objects.Ratio \
  ElementaryHolonics.Objects.RatioPhase \
  ElementaryHolonics.Objects.RatioBlock \
  ElementaryHolonics.Millennium.Turn \
  ElementaryHolonics.Millennium.Coupling \
  ElementaryHolonics.Millennium.HolonicPolygonalTorusCarrier \
  ElementaryHolonics.Millennium.HolonicSnellInteraction \
  ElementaryHolonics.Millennium.NavierStokesH2TriadMultiplierSwing \
  ElementaryHolonics.Framework.Objects \
  ElementaryHolonics.Framework
```

The new owner, Ratio/RatioPhase/RatioBlock, retained `Turn`, its remaining direct research
users, `Framework.Objects` and the combined `Framework` all built. Removing the old Turn import
exposed Mathlib log and trigonometric derivative APIs that Ratio had received transitively; Ratio
now imports `Mathlib.Analysis.SpecialFunctions.Log.Deriv` and
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` directly. The final affected build logs
contain no `sorryAx`, declaration using `sorry`, or error; the new theorem's axiom audit lists only
`propext`, `Classical.choice` and `Quot.sound`. The combined Framework gate completed 9,199 jobs.
Commands and logs are pinned in `docs/VERIFICATION_RECEIPTS.tsv`.

These checks preserve both the new core owner and the source-specific direct users of the retained
Turn owner. The eventual acceptance gates remain `lake build Holonics` and
`lake build HolonicsResearch` after the new roots and remaining cuts exist.
