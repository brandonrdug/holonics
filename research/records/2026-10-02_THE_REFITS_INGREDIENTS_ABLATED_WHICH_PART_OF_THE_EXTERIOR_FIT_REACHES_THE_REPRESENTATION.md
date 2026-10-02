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

## 3. The plain-gradient path's own comparison

The `sgd` arm re-run on seeds 202 and 303 with its comparison read every 10 steps on a fixed set of 32
training requests, each re-read on its own trajectory ([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/),
`path_sgd_*.txt`; both again end at 57 whole sections).
- **It climbs above where it started.** Seed 202's opening comparison `1.612090` is exceeded at step 30
  (by `0.001471`); seed 303's `1.608452` at step 60 (by `0.131100`).
- **Its excursions above the running minimum** (the step a rise begins, the step the minimum is
  undercut again, the peak rise): seed 202, ten excursions of 20 to 50 steps, peaks `0.002` to
  `0.116`; seed 303, eight of 20 to 60 steps, peaks `0.005` to `0.481` (steps 50 to 100, the largest,
  then `0.303` over steps 170 to 200). Each later excursion ends below the earlier minimum.

[agent-inferred] The path that reaches the sections is not monotone in its own comparison at any
window, and on one seed it rises well above the opening. A guard that admits a rise only below the
running maximum of a window of adopted comparisons cannot follow it; it needs an excursion above a
checkpoint, bounded in height and length, with the certified decrease owed over the excursion as a
whole. The numbers above are the measurement such a law's window and schedule read.

## 4. The native own release's jump, per decision, beside the float path's flips

The Lean thread's revision of #202 splits a move's change of the own release into the fixed mask's
change (continuous) and the flip. Both paths were read under that split
([receipts](2026-10-02_THE_REFITS_INGREDIENTS_receipts/): `m7_decision_diff.txt`,
`kinetic_chain_m0_m7.txt`, `split_sgd_303.txt`, `flips_sgd_303.txt`). Native values are lower ends in
units of `1/4096` nat, each within `6/4096`.

- **m7's flip is one request's lock order.** At `η = 1/2048`, request 3 goes from `43957` to `77944`
  (`+33987`). The other seven requests each fall, by `306` in total. Request 3's released section is
  the same before and after (all eight stations at 3, right at two). Six of its stations are read at
  different partial sections, and three term tops flip (stations 3, 6, 7). Per station: 1 `+2742`, 2
  `−105`, 3 `+6100`, 4 `+11986`, 6 `+9452`, 7 `+3815`, 0 `−4`, 5 `−2`. The lock-gap ranking swaps
  which near-tied station locks first in a degenerate release.
- **Per rung** (realized fixed-mask decrease `d`, flip `own − mask`):

  | η | `d` | flip |
  |---|---|---|
  | 1/16 | 33562 | 74106 |
  | 1/32 | 20269 | 45891 |
  | 1/64 | 10853 | 34325 |
  | 1/128 | 5523 | 34174 |
  | 1/256 | 2804 | 34100 |
  | 1/512 | 1419 | 34065 |
  | 1/1024 | 714 | 34047 |
  | 1/2048 | 359 | 34038 |

  From `1/64` down, the flip moves by `287` while `d` halves with each rung: a fixed cost. With the
  window bound `(flips + σ)/d`, paying it takes 95 moves at `1/2048`, but about 4 at `1/64` and 3 at
  `1/32`, if the flip held. Only the `1/2048` diff was taken; that the same request carries the flip
  at the other rungs is inferred from its constant size. m6 adopted at `1/2048` (`d = 361`, no flip)
  and flipped from `1/1024` up.
- **The float path's excursions are not flips of this kind** (`sgd`, seed 303, 32 fixed requests,
  10-step windows to step 130).
  - Trajectories change on 29 to 32 of the 32 requests in every window to step 200, falling to 2
    by step 390. Yet the flip part per window stays between `−0.0714` and `+0.0555` nats per term,
    takes both signs, and nets `−0.0247` over the 130 steps.
  - The excursions are in the continuous part: single steps raise the fixed mask itself, by
    `+0.7996` per term at step 57 (the excursion over steps 50 to 100), and by `+0.256`, `+0.251` and
    `+0.315` at steps 1, 77 and 78. Later steps repay them. The float path steps on minibatches of
    other requests, so its read mask can rise. The native move steps on the requests it reads, so its
    mask falls, and its only rise is the flip.
  - Per term, m7's flip (`34038/64`, between `531/4096` and `532/4096`) exceeds every float window's
    flip part (at most `227/4096`), and it sits in 1 of 8 requests.
- **Steps per move.** Native `η = 1/32` moves (m0 to m3) lower the fixed mask by `573/4096` to
  `574/4096` per term. A float step lowers it, per term:
  - `21/4096` to `22/4096` at the net mean over 130 steps;
  - `64/4096` to `65/4096` over the first 10 steps;
  - `101/4096` to `102/4096` at the median descending step.

  One `1/32` move is therefore 26 to 27, 8 to 9, or 5 to 6 float steps by those three rates. The
  float excursions' 20 to 60 steps come to about 1 to 3 native `1/32` moves at the net rate, or 3 to
  7 at the opening rate. The two per-term means average different families: the float averages every
  open station at every lock snapshot (about 36 terms per request), the native one term per station.
  So the ratio is an enclosure of scale, not an identity.

[agent-inferred] The float path never pays a flip like m7's because it never makes one: its flips
are many, small and of both signs. A window sized on the float excursions (about 1 to 7 moves) admits
m7's flip only at rungs of `1/64` or more, where `d` is large enough. The flip itself is a near-tie in
one request's lock order, a degeneracy of the release rather than of the move's size, so the
location this read points to is the release's lock ordering among near-tied stations.
