# Publication note

This directory publishes the compact receipts of the two Lean source lanes of the
[recovered-relations record](../../2026-10-09_THE_RECOVERED_RELATIONS_JOIN_AT_THEIR_RECEIVERS_AND_KEEP_THEIR_REMAINDERS.md)
(Refs #62, #63). Each lane's exact source was checked alone by the sole queue,
`lake env lean -j1 <file>` from its own worktree's `lean/`, on one CPU with the cached providers and a fixed
deadline that never changed between attempts. Every attempt is kept, the failed ones included.

## The finite torus subgroup receiver

`HolonicsResearch/Geometry/FiniteTorusSubgroupReceiver`, kernel-checked at sha256 `325bf52b`
([handoff](torus-native-v3/HANDOFF.md), [validation](torus-native-v3/VALIDATION.json),
[kernel validation](torus-native-v3/KERNEL_VALIDATION.json)).

| Attempt | Source sha256 | Exit | Compiler wall ns | Peak child RSS KiB | Result |
|---|---|---:|---:|---:|---|
| [v1](torus-native-v1/HANDOFF.md) | `190b46e8…` | 1 | 7,670,093,179 | 3,779,500 | 13 elaboration errors; 7 of 9 submitted queries carry `sorryAx` |
| [v2](torus-native-v2/HANDOFF.md) | `f71efe93…` | 1 | 16,290,268,458 | 3,864,344 | 3 elaboration errors; all 37 queries submitted, `sorryAx` present |
| [v3](torus-native-v3/HANDOFF.md) | `325bf52b…` | 0 | 13,505,240,845 | 3,805,680 | 0 errors; all 37 public theorems on the standard axioms only |

The fixed deadline was 91,287,144,808 ns throughout. The owner repaired proof bodies only, and the 37
statement headers of v3 equal v2's.

## The modular scattering residual

`HolonicsResearch/Zeta/ModularScatteringResidual`, kernel-checked at sha256 `9c28f550`
([handoff](modular-native-v3/HANDOFF.md), [validation](modular-native-v3/VALIDATION.json),
[kernel validation](modular-native-v3/KERNEL_VALIDATION.json)).

| Attempt | Source sha256 | Exit | Compiler wall ns | Peak child RSS KiB | Result |
|---|---|---:|---:|---:|---|
| [v1](modular-native-v1/HANDOFF.md) | `623e2430…` | 1 | 22,321,786,202 | 6,717,104 | 2 elaboration errors; 6 of 10 queries carry `sorryAx` |
| [v2](modular-native-v2/HANDOFF.md) | `b79985da…` | 1 | 22,865,632,233 | 6,722,256 | 1 rewrite error; `sorryAx` present |
| [v3](modular-native-v3/HANDOFF.md) | `9c28f550…` | 0 | 15,621,323,402 | 6,628,884 | 0 errors; all 10 public theorems on the standard axioms only |

The fixed deadline was 154,785,618,970 ns throughout. The first v3 admission was refused before any
compiler launched, for insufficient measured memory headroom; the later admission ran once under the
same bounds. The refused admission and every compiler failure are kept.

## Projected host paths and hashed files

- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). The handoffs and validations name the
  lanes' worktrees, the Lean toolchain and the home directory. Four placeholders are declared for them,
  `<torus-worktree>/`, `<modular-worktree>/`, `<lean-toolchain>/` and `<home>`, replaced longer
  prefixes first. There is no other byte change, all 12 entries invert to their pinned originals, and no
  host path remains.
- **Hashed only:** each packet's `OMITTED.md`. That covers the copied sources, the compiler requests,
  provider pins and seals, and lifecycle receipts, among them the output seals over the compact limit.
- **Scope.** Each check certifies the exact source alone, its compiler exit and its public-theorem axiom
  reports. The library build of the integrated aggregate is a separate gate. No native consumer, HNN
  behaviour, estimate or target theorem is claimed.
