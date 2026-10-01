# The decision margins through the accepted move: the comparison read the open section, and the release decided elsewhere

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured], read-only,
on saved states; [agent-inferred] where marked. Receipts:
[`2026-10-01_THE_DECISION_MARGINS_receipts/`](2026-10-01_THE_DECISION_MARGINS_receipts/).

## 1. The question

The witness's metric admitted a move from c6 where the coordinate control was refused
([one guarded move](2026-10-01_ONE_GUARDED_MOVE_MEASURED_THE_WITNESSS_METRIC_ESCAPES_C6_WHERE_THE_CONTROL_IS_REFUSED_AND_THE_DECISIONS_DO_NOT_FOLLOW.md)).
The executed `L` fell, yet stations right fell from 15 to 13. Astra asked where that discrepancy
arises, term by term, before any objective is replaced or any longer run is launched.

`executed margins` (`hnn::executed::move_margins`) reads the move from c6 to its adopted successor
on the guarded witness's batch. For every one of the 64 decision terms it reads:
- the lock face at `before`, and at `after` on the same fixed section, so the change is the
  constitution's alone;
- the top class, and the target's and the leading rival's growth enclosures;
- the proposal's own first-order bound on the exact storage move.

It also reads each request's released section before and after. All 64 terms are kept; none was
selected after the outcome.

## 2. What the move did to the terms the comparison reads

- **Where the terms sit.** All 64 are read at refinement 0 (open section, nothing placed), except
  requests 5 and 6, which are read at refinement 1. A term is read at its lock's refinement only
  before `r*`, the last refinement whose placed cells all equal their targets. Six of eight requests
  locked a wrong class first, so `r* = 0` and every station is read at the open section.
- **The move improved those terms.** `ℓ` fell on 42 terms by `184959/65536` nats in all, and rose
  on 22 by `58699/65536`, a net fall of `126260/65536`.
- **The linear model held.** The first-order bound's sign agrees with the finite change on 60 of 64
  terms.
- **The ordering moved the right way.** The target-versus-best-rival margin widened on 44 terms and
  narrowed on 20. At the open section the target became the top class on 3 more stations
  (22 to 25), and lost it on none.
- **One first lock came right.** Request 3's first lock moved from station 7 (wrong) to station 6
  (right). First locks are right in 3 of 8 requests after the move, against 2 before.

## 3. Where the decisions went

The release decides every station after the first in a context the comparison never read: the
earlier locks are placed, and those cells are not their targets. Five requests changed their lock
order. Their stations were decided in new contexts:
- **Lost:** request 0 station 1, request 1 stations 5 and 6, request 3 station 1, request 7
  station 4.
- **Gained:** request 1 station 4, request 3 station 6, request 6 station 2.

These flips are not explained by their open-section terms. Request 3 station 1 is the target's top
at the open section both before and after, and is lost in the release. Request 1 station 4's
open-section top stays wrong, and the release gains it.

[agent-inferred] **The receiving law the comparison retains.** At the decisions, the comparison
reads each station's lock once at the refinement that decided it, or at `r*`. Once a request's
first lock is wrong, that is the open section for every station. So the descent covector carries
the open-section readings, and the release's actual decisions after the first lock carry no
covector at all. The executed `L` is the right quantity for the readings it contains, and those
readings did improve: 25 targets on top, against 22 before. But they are not the readings that
decide 7 of the 8 stations of a request whose first lock is wrong.

The discrepancy is a coverage fact of the reading, not a failure of the step: the first order held
on 60 of 64 terms. It is also not a reason to read in wrong contexts. A context whose placed cells
are wrong is not one the trained receiver should be shaped to.

## 4. What it names

The decisions that matter follow the first lock. The release chooses that lock by its own rule: the
station with the largest gap between its top and the rest locks first. The lock order is read
beside the comparison (`OrderReading`) but has no term in it. Two earlier results bear on it:
- the segment probe found that the first lock lands on the far end at the founded transport and on
  a near station at `ρ*`;
- here, the one right first lock the move produced came with `ρ` moving toward `ρ*`.

So the next subject is the order: the gap rule that picks the first lock, read as a term of the
comparison at `r*` on the release's own covectors. It is the lock's own decision law, not an
authored target order.

## 5. Time and resources

| Run | Projection | Deadline | Measured wall | Peak resident |
|---|---|---|---|---|
| margins, 19 threads | 176,743 ms (one compare, one mask reread, one incumbent read with covectors) | `timeout 177`, per-line bound 176,743 ms | 83,276 ms, exit 0 | 167,911,424 bytes |

Measured over projected: `83276/176743`.
