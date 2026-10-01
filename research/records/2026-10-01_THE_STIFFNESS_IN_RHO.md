# The stiffness in ρ: the stall is a basin of the comparison, not a fault of the metric

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured],
read-only; [agent-inferred] where marked. Receipts:
[`2026-10-01_THE_STIFFNESS_IN_RHO_receipts/`](2026-10-01_THE_STIFFNESS_IN_RHO_receipts/).

## 1. The question

Under the order term and the witness's metric, five guarded moves from c6 raised stations right to 19
and then stalled. In those five moves `ρ` moved `17466/2^21` of a `541877/2^21` chord to the refit's
`ρ*` ([the order measured](2026-10-01_THE_ORDER_MEASURED_ONE_MOVE_FROM_C6_GAINS_STATIONS_WHERE_THE_LOCK_FACE_ALONE_LOST_THEM.md)).
Two causes were possible:
- **the plane's `E` direction.** The move's plane is spanned by the source port's own unit step,
  and a different `E` change might free `ρ`;
- **the comparison itself.**

## 2. Not the plane's `E` direction

`executed route-plane` reads the witness's form on the plane of the route `E* − E` (the refit's
`E`) and `ρ`, against the move's own plane:

| State | Plane | `β` over the chord |
|---|---|---|
| c6 | the port's unit move | `9539727/2^29` over `541877/2^21`, between `1/15` and `1/14` |
| c6 | the route | `7748797/2^27`, between `1/18` and `1/17` |
| move 3 (stalled) | the port's unit move | between `1/107` and `1/106` |
| move 3 (stalled) | the route | `−3995139/2^32`: away from `ρ*` |

`G_ρρ` is the witness's own and does not depend on the plane's `E` direction (`15487189/512` at c6,
`6917875/128` at move 3). At move 3 the comparison's slope in `ρ` has turned. `g_ρ` reads
`−11954551/262144`, so the comparison now asks for a higher transport. The route's plane, with its
cross term, sends `ρ` away from `ρ*`.

## 3. A basin: the chord from the stalled state rises before it falls

`executed segment arm=order-dec` reads the straight chord from move 3's state to the refit (the
fifths, where `ρ` stays on the port's lattice):

| `s` | `L + O` (`/4096` nats) | Solved | Stations right | First locks right |
|---|---|---|---|---|
| 0 (move 3) | `[424353, …)` | 1 | 19 | |
| 1/5 | `[483256, …)` | 6 | 17 | 3 |
| 2/5 | `[479489, …)` | 8 | 27 | 2 |
| 3/5 | `[413803, …)` | 21 | 23 | 2 |
| 4/5 | `[330280, …)` | 30 | 22 | 2 |
| 1 (refit) | `[150580, …)` | 45 | 55 | 8 |

- From the stalled state the comparison rises by `58903/4096` nats over the first fifth, and falls
  below the stalled state's value only past `3/5`.
- At `1/5` and `2/5`, `r*` stays at 0 or 1 in every request, as at the stalled state. The rise is in
  the same kind of terms (open-section locks and orders), not a change of reading set.
- The decisions disagree with the comparison along the first stretch. Solved goes 1, 6, 8 while
  `L + O` rises, and stations right reach 27 at `2/5`.

[agent-inferred] The stall is a basin of the comparison. The learned state sits in a local minimum
of `L + O` separated from the refit's region by a rise, and inside the basin the comparison's
`ρ` slope points up. The witness's metric is not at fault: it reads the basin truly. The segment
probe found the chord from the founded opening to the refit descending strictly under the lock face.
So the descent from the opening chose a different valley. That choice is made by `E`'s direction,
which comes from the source port's normal law and was nearly orthogonal to the route at the
opening ([the native direction](2026-10-01_THE_NATIVE_DIRECTION_MEASURED_THE_STEP_DESCENDS_THE_EXECUTED_RELEASE_WITHIN_ITS_CELL_AND_GATE_A_ADOPTED_SIXTEEN_TIMES_BEYOND_IT.md)).

A second fact stands beside it. Along the first two fifths the comparison and the decisions move
in opposite directions. Even a summed lock face with order terms does not track decision quality
there.

## 4. What it names

- **`E`'s direction under the witness.** The witness's metric now sizes the plane, but the plane's
  `E` direction is still the normal law's, measured by the port's retained Gram, a different
  receiver. The witness's own direction in all of `E`, its form pulled back over every entry, is the
  next law to state. Only it can choose the valley at the opening. Its size, `600` entries of `E`
  against about `400` sheets, makes it a dual solve on the sheets (the Gram's inverse beside it), not
  a dense one in `E`.
- **The comparison against the decisions** along a path, where the two disagree, stays open.

## 5. Time

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| route plane, both planes (first launch) | `4 · 78,889` ms | per-line 78,889 ms | stopped early at 79,355 ms: the bound was the lock face arm's plane line, not the order arm's (a projection error) | |
| route plane, the route only | `2 · 262,311 = 524,622` ms (the order arm's measured move at c6 bounds a plane read) | `timeout 525` | 187,831 ms, exit 0 | 265,584,640 bytes |
| the chord, 5 points | `5 · 95,868 = 479,340` ms | `timeout 480` | 207,859 ms, exit 0 | 119,218,176 bytes |

The declared read was narrowed after the early stop, with the per-line bound taken from the order
arm's own measured unit. Nothing was raised past a measurement. Measured over projected:
`187831/524622` and `207859/479340`.
