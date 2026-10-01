# The segment probe measured: the lock face sees the refit, the chord descends to it, and its reading needs the lower modulus

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured] for every
count, enclosure and listing, read once under the
[pin](2026-10-01_THE_SEGMENT_PROBE_PINNED_BEFORE_ITS_RUN.md) (`4b4531be`; launcher corrected at
`b2bcaa68`); [agent-inferred] where marked. Read-only: no move, no update, no fit, no law changed.

The computational object is the helical pair interaction, read through the receiving bank's complex
parametrons at the decisions. Of the [winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s
objects it touches **faces and placement** (each decision term read at the section the release placed)
and **the tube** (the span's transport modulus). The helix, the pair, the cell holonomy and the tower
thread stay attached and unchanged.

## 1. The reads

`hnn_prediction -- executed segment order2 2026093061 8 …`: gate A's development batch, read by gate
A's comparison (the lock face at the decisions). `Θ₀` is the founded opening. `Θ*` is the
station-framed refit, remounted from `E` and `ρ` alone (labelled partial on the error stream). The
chord points are `Θ₀ + s(Θ* − Θ₀)`, exact in `E` and in `ρ`.

| Constitution | `ρ` | `L` (nats) | Solved of 64 | Class holds | Stations right of 64 | Whole of 8 | First lock right of 8 (its stations) | Held terms |
|---|---|---|---|---|---|---|---|---|
| `opening` (`Θ₀`) | `102837/131072` | `[500197/4096, 500203/4096)` | 0 | 13 | 15 | 0 (7 released) | 0 (6: 3, 7: 5) | 56 |
| `chord-1/4` | `754595/1048576` | `[448621/4096, 448627/4096)` | 0 | 13 | 16 | 0 | 1 (5: 1, 6: 2, 7: 5) | 55 |
| `chord-1/2` | `343247/524288` | `[375687/4096, 375692/4096)` | 10 | 20 | 23 | 0 | 1 (6: 1, 7: 7) | 55 |
| `chord-3/4` | `618393/1048576` | `[339158/4096, 339163/4096)` | 27 | 37 | 25 | 0 | 0 (6: 2, 7: 6) | 56 |
| `refit` (`Θ*`) | `137573/262144` | **`[133292/4096, 133295/4096)`** | **45** | 57 | **55** | **5** | **8** (3: 1, 4: 2, 5: 5) | 8 |
| `refit-founded` (`E*` at `ρ₀`) | `102837/131072` | `[310210/4096, 310215/4096)` | 15 | 33 | 22 | 0 | 4 (3: 1, 5: 1, 7: 6) | 44 |
| `gateA-best` | `1646645/2097152` | `[517184/4096, 517189/4096)` | 7 | 14 | 16 | 0 | 2 (7: 8) | 54 |

Threshold holds at every decision term of every constitution except the opening (50) and `chord-1/4`
(63). Where the lock face's terms lie (`terms_summary.txt`):

| Constitution | `ℓ < ln 2` (solved) | Between | `ℓ`'s lower end at least `105476/65536` (`ln 5`'s grain cell or above) |
|---|---|---|---|
| refit | 45 | 17 | 2 |
| refit-founded | 15 | 35 | 14 |
| chord-3/4 | 27 | 14 | 23 |
| chord-1/2 | 10 | 29 | 25 |
| chord-1/4 | 0 | 30 | 34 |
| opening | 0 | 20 | 44 |
| gateA-best | 7 | 17 | 40 |

**The identity controls hold.** `opening` reproduces gate A's constitution 0: solved 0, released 7,
15 right, the same `L`, held 56. `gateA-best` reproduces its constitution 1: solved 7, released 8, 16
right, the same `L`, held 54. The run therefore reads exactly what gate A read.

**The refit's releases on gate A's batch.** These are synthetic order-2 sections. Each row gives the
target and then the release.
- Five are whole.
- Request 0 releases `1 1 2 2 3 3 0 0` against `2 1 3 2 0 3 1 0`: every even station copies its odd
  neighbour.
- Request 5 releases `1 0 1 1 2 2 3 3` against `1 0 2 1 3 2 0 3`: the same lag-1 copy from station
  2.
- Request 6 releases `3 0 0 1 0 2 1 3` against `3 0 0 1 1 2 2 3`: the even chain falls one class
  behind at stations 4 and 6.

These are the station-framed record's secondary cause, seen again on an unseen batch. Every section
is in `segment.txt`.

## 2. Against the outcome rules fixed before the run

- **(P) holds: the path, not the objective.** The refit reads 55 stations right (more than 24) and 5
  whole sections. Its `L`, whose upper end is `133295/4096`, lies below gate A's lowest
  (`[342226/4096, …)`) by disjoint enclosures. The lock face at the decisions ranks a working
  constitution far below everything gate A's 16 moves reached.
- **The chord descends strictly** from `Θ₀` to `Θ*`: each point lies below the last by disjoint
  enclosures. A descent path from the opening to a working constitution exists, and the native move
  did not take it.
  - The descent is unequal along the chord. The first three quarters take `L` from `[500197/4096, …)`
    to `[339158/4096, …)` with stations right from 15 to 25 and no whole section.
  - The last quarter takes it to `[133292/4096, …)`, with 55 right and 5 whole.
  - Gate A's lowest `L` sits at about `chord-3/4`'s, where the stations are still near a guess.
- **(M) holds: the reading needs the lower modulus.**
  - The refit's own `E` at the founded `ρ₀` reads 22 right (at most 24) and no whole section. At
    `ρ*` it reads 55 right and 5 whole.
  - Gate A's modulus never left `[809211/1048576, 829845/1048576]`.
- **(O) does not hold.** No outcome of the pin was left undecided.

**What it cannot show.** It cannot show whether native deposition reaches the refit or any other
working constitution. The chord is one path, and the refit is one exterior fit among the
constitutions that might work.

## 3. What the listings show at the decisions [measured; the reading agent-inferred]

**The first lock decides the section, and the modulus decides the first lock.**
- At `Θ*` the first lock falls on stations 3 to 5 and is right in all 8 requests, and 8 of the 64
  terms are held.
- At `ρ₀` the release locks the far end first (station 7 in 6 of 8 requests for `E*` at `ρ₀`, in 8 of
  8 at gate A's best) and is mostly wrong there. That puts `r*` at 0 and reads most decision terms
  from the open section or one lock in (held 44 to 56).

[agent-inferred] **Why the far end locks first at the founded modulus.** From the open section,
station `j`'s span is its candidate and the 40 request cells, at distances `j + 1` to `j + 40`.
Under the station-framed weights, the request's total weight relative to the candidate is
`W_j(ρ) = Σ_(d=j+1)^(j+40) ρ^d` (read exactly with rationals).
- At `ρ₀`, `W_7` lies between `13/20` and `7/10`. The far station's candidate still meets a heavy
  request, which enters through cells eight or more ticks back and carries the other chain and the
  terrain's period as well as the seed. The largest gap lands at the far end, and the lock there is
  not the key's.
- At `ρ*`, `W_3` lies between `3/20` and `1/6`, `W_5` is below `1/20` and `W_7` below `1/50`. The far
  stations read almost only their own candidate. The gaps that order the locks come from the near
  stations, where the last request cells weigh most, through `E*`'s reading. A near station locks
  first, and its lock is right.

This is the re-entry diagnosis's "far end first" order, now read at the decision itself rather than
after a re-entry. The modulus, not the normalization's index set, decides it.

## 4. What this locates, and the next loop's subject

**The blocker, by its measurement.** The lock face at the decisions descends strictly along a chord
from the founded opening to a constitution that reads order-2. That constitution solves 45 of 64,
reads 55 stations right and 5 sections whole on gate A's unseen batch, and its reading needs the
transport modulus near `137573/262144`. Gate A's certified moves held the modulus within
`[809211/1048576, 829845/1048576]`. There the refit's own `E` reads 22 right and locks the far end
first, and gate A's best `L` stalls at `chord-3/4`'s level.

**The next loop** (agent-inferred, the smallest that discriminates; read-only):
- Read the modulus's part of the lock face at the decisions at gate A's constitutions and along this
  chord:
  - the slope `γ_ρ` with its sign;
  - the least-squares unit move `−γ_ρ/G_ρ` against the chord's `Δρ`;
  - the joint step's `ηΔρ` as the move actually takes it.
- It separates two causes:
  - **a sign obstruction**: `γ_ρ` does not point down at `ρ₀` with gate A's `E`, so descent in `ρ`
    appears only once `E` already reads the rule;
  - **a scale obstruction**: `γ_ρ` points down, but the joint step, sized by `E`'s entry scale,
    moves `ρ` by far less than the chord needs.
- The owner is `hnn::executed`'s committed move (`modulus_least_squares`, the ladder's joint unit
  move). The harness's `executed slopes` reads only the hinge at every refinement today.

## 5. Time, memory and identities

| Read | Measured | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| the probe, 7 constitutions at 19 threads | 259,811 ms (the launcher), 259,275 ms (the harness) | 319,144 ms / `timeout 320` | 122,744,832 |

- **Per constitution**: 38,586, 39,079, 38,965, 40,994, 40,036 and 41,070 ms, and the opening 20,496
  ms (7 of its 8 requests released). Each is below the per-unit bound of 45,592 ms, and no early
  stop fired. Measured against projected: `259811/319144`.
- **The first launch** failed to start the harness (`/usr/bin/time` is not on this host; exit 127 in
  1,004 ms). Nothing was read, and the launcher was corrected before the second launch. No limit
  was changed.
- **Identities** (`identities.txt`): source `4b4531be`; binary sha256
  `0ee7c9931bee520e9ee041b7312214286ed651ec69cc41c5016b58cea77511c1`; refit sha256
  `5d8c4a2c7369ef23cbfbe7bdf80ea3dbe398b97e191f5fafcba39fa2d97f7fa5`; `witness_best.state` sha256
  `697ecec94d86e4abf242e8e1541cabe176b1d70c75c360cd3bb399d58f3e3073` (the same as gate A's and
  c2's).

Gates: `cargo check --workspace --all-targets` is clean. No library code or Lean changed, so the
library tests and the Lean build were not run.

The receipts (`2026-10-01_THE_SEGMENT_PROBE_receipts/`, synthetic terrain only) are:
- `segment.txt`: every constitution's line, every request's release and every decision term whole;
- `segment.err`: the partial-remount labels;
- `identities.txt`;
- `terms_summary.txt`, from `research/notebook/hnn_design/segment_terms.py`.
