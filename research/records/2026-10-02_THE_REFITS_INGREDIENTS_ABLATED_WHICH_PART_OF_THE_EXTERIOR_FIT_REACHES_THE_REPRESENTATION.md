# The refit's ingredients ablated: which part of the exterior fit reaches the representation

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured],
exterior float probe; [agent-inferred] where marked.

## 1. The question, fixed before the runs

Step 1's blocker stands as the kinetic move left it: every native move descends the comparison and
none reaches the decisions, while the station-framed refit (96 whole sections of 128 on order-2's
held-out requests) shows a representation exists
([the station-framed placement](2026-09-30_THE_STATION_FRAMED_PLACEMENT_MEASURED_THE_REFIT_READS_BOTH_CHAINS_AND_THE_CERTIFIED_MOVE_KEEPS_THE_MODULUS_AT_ONE.md) §2;
[the representation](2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md)).
The refit (`eO_fit.py`, retired with the notebook's probe at `e214ccc8`) differs from the native
move in its optimizer: float Adam on `E` with a cosine schedule (momentum `0.9` and a per-coordinate
second moment `0.999`), 400 steps of 16 requests re-read on the release's own trajectory, and `ρ` by
Adam on a central difference. The native moves are guarded certified steps in the port's or the
receiver's metric, a few at a time.

The claim this loop can make is narrow: which ingredient of the exterior optimizer carries it to the
representation. Four arms, every other setting the refit's (`order2 400 256 101 0.03 0.05 1 16`):
- `adam`, the refit (the reproduction: 96 whole expected);
- `rms`, the per-coordinate second moment without momentum;
- `momentum`, momentum without the per-coordinate scaling;
- `sgd`, neither.

The arms without the per-coordinate scaling take a global step matched to Adam's first step's
root-mean-square. **Acceptance of the location.** An ingredient is located when the arms that keep
it reach at least half the refit's whole sections (48 of 128) and the arms that drop it reach fewer
than a tenth of them; otherwise the optimizer is not the location, and the record says so. Nothing
native changes in this loop.

**What this loop's arms cannot show** (fixed before the arms finished). A lower loss or more whole
sections from an exterior float optimizer, read through a classification, is not the mechanism (the
kinetic move's record §2; the comparison-descent line is closed). The arms are diagnostic only: their
sole output is which ingredient matters. The loop's deliverable is that ingredient's native
counterpart, derived from the existing chain (the constitution's own update, its Fisher form, the
release's schedule), and its acceptance is the METHOD's: a return reaching a locus, changing its
constitution through that native law, and consumed on a later cut, with order-2's held-out sections
read natively. No Adam arm's number stands in for it.

## 2. Measured

Held-out whole sections of 128 at step 400 (the best checkpoint in brackets), three seeds per arm
([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/)):

| Arm | seed 101 | seed 202 | seed 303 |
|---|---|---|---|
| `adam` (the refit) | 36 (43) | 46 (53) | 49 (52) |
| `rms` (no momentum) | 54 (54) | 72 (72) | 47 (52) |
| `momentum` (no per-coordinate scale) | refused at step ~300, a singular solve (34) | 31 (45) | refused (36) |
| `sgd` (neither) | 18 (27): `E` ran to its bound at step 200 and `ρ` back to one | 57 (57) | 57 (71) |

- **The reproduction.** The float refit reaches 36 to 49 whole sections, not the record's 96. That
  96 was the exported `E` read natively after rounding to the lattice (the station-framed record
  §2); the float release here is the probe's own, and the run-to-run spread is large (the same arm
  moves by 10 to 20 sections between checkpoints).
- **No ingredient is located.** Plain gradient steps with the matched step size reach 57 on two of
  three seeds, as many as the scaled arms; the per-coordinate scale is not required, and momentum is
  not either (it destabilizes the solve). The acceptance's location test is not met by any arm.

[agent-inferred] What the float fits share and the native moves lack is not the metric: every arm
takes 400 small, decaying, stochastic steps, each accepted whatever it does to the comparison,
re-read on the release's own trajectory. The Lean thread's baseline (#195) proves every candidate
move is a gradient step under some metric and stops only where the gradient vanishes; the native
chain stopped first at its guard (`OwnNotBelow`, the executed release must fall). The step-1
records found the chord to the refit rising before it falls (the stiffness record). So the next
candidate location is the guard together with the step schedule, read first on the float path
itself: whether the plain-gradient arm's own comparison rises along its way to the sections.
