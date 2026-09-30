# The re-entry diagnosed: a later lock takes the span's mass and quenches the earlier stations

**Date.** September 30. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [measured] for the native
exact reads (an exterior diagnostic harness on synthetic terrain, not a pinned run);
[agent-inferred] where marked, for the mechanism's reading and the repair, which is not built.

**Occasion.** The [passage law's measured record](2026-09-30_THE_PASSAGE_LAW_MEASURED_THE_FRONTIER_READS_THE_REQUEST_AND_A_LOCKED_NEIGHBOUR_ERASES_THE_OTHER_CHAIN.md)
§3 left one blocker: from the open section the fitted constitution reads 972 of 1,024 station tops
right, and with the other chain's locked data placed at their truth, 273. The
[pin's](2026-09-30_THE_PASSAGE_LAW_THE_SECTION_CONTINUES_THE_REQUEST_AND_THE_TRANSPORT_WEIGHS_ITS_FRONTIER.md)
development reads (§4) had teacher-forced fits at `ρ = 13/20` and `1/2` release 128 of 128 whole
sections in clock order and none in the largest-gap order. GPT-6 Astra named three mechanisms, not
exclusive: **(D)** denominator dilution (each datum weighs by its age at the span's common end, so a
late lock enlarges the normalizing mass and weakens the existing evidence); **(I)** the re-entered
datum's own amplitude interfering through the nonlinear monodromy; **(O)** order dependence (the
release locks the largest gap first, at stations 3 to 7). This diagnostic tells them apart.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches **faces and
placement** (each datum's transported weight, the object under test), **the tube** (the request
and its section one clocked span), **the helix** (the placed phases) and **the cell holonomy** (the
bank's monodromy over the turn); the pair and the tower thread stay attached.

## 0. The recorded failures this diagnostic could repeat, and how each was avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **1 and lesson 5 (an authored routine; no catered machinery).** Nothing the machine runs changed:
  no library code. The three storages are exterior interventions routed through the owners
  (`BankPlacement::{storage, weights}`, `ReceivingBank::read_turn`); the clock-order release is a
  diagnostic order, not a law; truth only places the correct data and assesses.
- **3 (a located cause carried unrepaired into a new consumer).** No consumer is built. The cause
  stays open in `BankPlacement` and `bank_release`; its repair is stated in its owner (§6), not
  built.
- **6 (seen graded as unseen).** The 16 requests are development held-out draws (seed
  `41 + 1,000,003`), never read by this fit's training (seed 101) and not Stage 0's held-out set.
  No transfer is claimed.
- **7 (a local pass read as progress).** The open section's 9 whole sections (§5) are an
  intervention's reading, not a release; nothing is claimed as an improvement.
- **9 (a refusal answered with a larger limit).** Projected from one request, run once inside the
  projection, not rerun.
- **10 (report substance).** The mechanism is located by exact margins; the float prototype is an
  exterior cross-check only.
- **11 (the programming language).** The question is a transport's modulus, a span's transported
  mass and the pump's lock window; the three storages and the replay are its realization.

Every margin below is an exact enclosure from the native owner; no decimal is reported.

## 1. The run

**Frozen material.** The seed test's fit (the passage law's receipts, `seed_export.txt`), rounded to
the source port's lattice `2^(−21)`: `ρ = 1452225/2097152`, `E`'s largest entry `2519969/1048576`.
No learning.

**Requests.** 16 development held-out order-2 requests, the first of each seed pair
`(x_38, x_39) ∈ 4²` in the draw's order (81 draws; `bank_causes_probe/eD_reentry.py`). Station `2k`
continues `x_38`, station `2k + 1` continues `x_39`.

**Replay.** Each request's correct partial section is placed in two orders: clock order, and the
lock order its own ordinary release records (`generate_by_bank`, the largest gap first). At every
insertion `k` (the first `k` stations of the order placed at their truth), every open station's
five candidates are read by the bank from three storages:
1. **full**: `BankPlacement::storage(S ∪ {j: x})`, the passage's law;
2. **denominator alone**: `storage(S ∪ {j: x}) − Σ_(i∈S) w_i P^(λ−c_i) E e_(t_i)`, each re-entered
   datum's amplitude removed at the owner's own weight, so every remaining datum is weighed over
   the enlarged span's mass and no re-entered amplitude enters (the images are held to the owner
   by an exact identity asserted at every station and class pair);
3. **none**: `storage({j: x})`, the open section.

**The comparison** is `hnn::executed`'s class predicate on the joint growth enclosures: the rival is
the other class of the largest `upper`; the margin's enclosure is `[L_t − U_r, U_t − L_r]`; it
holds when `L_t > U_r` and fails when a rival's `L` reaches `U_t`; the threshold is `L_t > 1`. A
comparison is **lost** at insertion `k` when it holds from the open section and does not hold at
`k`. The trace records, at every insertion and for every intervention, the target's and the rival's
four member growths. Beside the replay: the ordinary release, and a clock-order release (the
owner's flip, threshold and Floquet certificate, one station a refinement).

## 2. The measurement

**Comparisons holding, of the open stations, by insertion** (16 requests):

| Order, storage | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| clock, full | 120/128 | 105/112 | 95/96 | 77/80 | 64/64 | 46/48 | 30/32 | 14/16 |
| clock, denominator alone | 120/128 | 108/112 | 93/96 | 64/80 | 33/64 | 8/48 | 0/32 | 0/16 |
| clock, none | 120/128 | 110/112 | 96/96 | 80/80 | 64/64 | 48/48 | 32/32 | 16/16 |
| release's order, full | 120/128 | **71/112** | 47/96 | 32/80 | **15/64** | 11/48 | 8/32 | 9/16 |
| release's order, denominator alone | 120/128 | **39/112** | 17/96 | 16/80 | **14/64** | 10/48 | 5/32 | 2/16 |
| release's order, none | 120/128 | 104/112 | 89/96 | 74/80 | **58/64** | 46/48 | 30/32 | 16/16 |

**The first loss** (requests, by the insertion at which a correct comparison is first lost):

| Order, storage | 1 | 2 | 3 | 4 | 5 | 6 | 7 | never |
|---|---|---|---|---|---|---|---|---|
| clock, full | 5 | 1 | 2 | 0 | 1 | 1 | 2 | 4 |
| clock, denominator alone | 2 | 2 | 8 | 4 | 0 | 0 | 0 | 0 |
| release's order, full | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| release's order, denominator alone | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

With no re-entry nothing is lost, by construction. Every first loss under the full placement is a
failure (a rival's lower end reaches the target's upper end), never an undecided comparison.

**The release's order.** In every request the release locks one whole chain first, all four locks
right (the odd chain in 14 requests, the even in 2), its first lock at station 7 in 11 requests, at
5 in 3, at 6 and at 4 once each. Insertion 4 of that order is the release's own decision point (13 of
its 15 first wrong locks come there): the other chain open, the locked chain placed at its truth. There 58 of 64 comparisons hold with no
re-entry, 15 under the full placement and 14 under the denominator alone. Of the 43 comparisons the
full placement loses there, the denominator alone loses 36; 7 need the added amplitude. The full
placement keeps every open target past one (58 of 58); the denominator alone leaves 56 of 58 below
one.

**The first lost comparisons, told apart** (each request's first loss under the full placement,
each lost station read under the denominator alone):

| Order | Lost (requests) | Lost also by the denominator alone | Lost only with the amplitude | Lag-1 neighbour placed | Rival = the neighbour's successor |
|---|---|---|---|---|---|
| the release's | 35 (15) | **28** | 7 | 10 | 3 |
| clock | 13 (12) | 4 | **9** | 12 | 4 |

At the release's first insertion the full placement drives every open target past one (112 of
112); the denominator alone leaves 34 of 112 past one, and each lost target's growth falls to
between `2^(−15)` and `2^(−7)` of its open-section growth. At clock order's first insertion the
denominator alone leaves every target past one (112 of 112).

**The weights behind it** (exact, at the fitted `ρ`, enclosed at grain `2^(−8)`). The request's
transported mass `Σ_(a=8)^(47) ρ^a` lies in `[11/64, 45/256]`. From the open section station 0's
candidate takes `[39/128, 79/256]` of its span. Station 7's lock has age 0 and modulus one: read
from station 0 it takes `[205/256, 103/128]` of the span, weighs `ρ^(−7) ∈ [209/16, 105/8]` times
station 0's candidate, and scales every other datum by a factor in `[25/128, 51/256]`; station 0's
candidate falls to `[15/256, 1/16]`.

**Two first losses, exactly.**
- Request 0 (seed pair 0 0), the release's order, insertion 1 (station 7 placed at 0), station 0
  (target 1). Open: holds, `[699/512, 701/512]` against class 2; member 3 attains it, the target
  `[9819/64, 78553/512]`, the rival `[19463/128, 77853/512]`. Full: fails, `[−3826, −7651/2]`
  against class 3; member 3, the target `[113667/4, 28417]`, the rival `[64485/2, 128971/4]`.
  Denominator alone: fails, `[−43/262144, −21/131072]` against class 3, every member of the
  target between `116991/524288` and `1855/8192`, below one. The far lock's mass quenches the
  evidence; its amplitude drives the bank far past one, and there the rival wins.
- Request 3 (seed pair 0 3), clock order, insertion 1 (station 0 placed at 1), station 1 (target 0).
  Open: holds, `[296501/1024, 593011/2048]` against class 2; member 3, the target
  `[82893/256, 41447/128]`, the rival `[70141/2048, 35071/1024]`. Full: fails,
  `[−9495/512, −9493/512]` against class 2, the placed neighbour's successor; member 3, the target
  `[97111/512, 12139/64]`, the rival `[106605/512, 53303/256]`. Denominator alone: holds,
  `[35789/2048, 143159/8192]`. Here the neighbour's amplitude does the damage.

Every other insertion, station and member is in the receipts' trace.

## 3. Which mechanism the evidence supports [measured; the reading agent-inferred]

- **(O) Clock order does not rescue the full placement.** In clock order 12 of 16 requests still
  lose a correct comparison, 5 at the first insertion (station 1 once station 0 is placed), and the
  clock-order release is whole at 2 of 16 against the ordinary release's 1. What the order changes
  is which datum re-enters first: at the first insertion 105 of 112 comparisons hold in clock order
  against 71 of 112 in the release's.
- **(D) In the release's own order the damage is normalization.** Its first locks are among the
  span's newest data (station 7, age 0 and modulus one, in 11 requests). The first loss comes at the first insertion in 15 of 16 requests; 28
  of those 35 lost comparisons, and 36 of the 43 lost at the release's decision point, are lost by
  the enlarged denominator alone, which quenches the bank. The added amplitude does not restore
  them: it drives every member far past one, and the comparison is then read as a perturbation of
  the far datum's own resonance.
- **(I) Interference is secondary and local.** Where the dilution is mild (clock order: the placed
  data are older than the station read), 9 of 13 first losses need the added amplitude. 12 of 13
  have the lag-1 neighbour placed, and in 4 the rival is that neighbour's successor: `E`'s key reads
  a lag-1 datum of the other chain as a lag-2 seed.
- **The cause of (D), and why (O) matters.** The placement's weight `ρ^a`, with `a` the age at the
  span's end, is the one-way transport `ρ^(τ − τ_k)`, the same at every reading frame `τ`. For a
  datum after the station read, it is `ρ^(−(τ_k − τ_j))` times that station's own candidate: the
  farther a later lock lies, the more it weighs. The largest-gap order locks the far end first
  (from the open section, which holds only past data, a far station's candidate is the heaviest datum
  of its span, since the request lies farther from it), and under the one-way law those locks then
  take the span's mass from every earlier station. The pin's teacher-forced fits (§4 there) released
  whole in clock order; this on-policy fit, trained on the far-end-first trajectory, loses the lag-1
  comparisons that clock order places first.

## 4. The falsifier, read as written

- **A wrong comparison before any re-entry: does not fire.** The ordinary release's first wrong lock
  (15 requests) never comes at the first refinement: 13 come after four correct locks, 2 after five.
- **Removing re-entry does not restore it: fires at 4 of 15.** At 11 of the 15 first wrong locks the
  station's comparison holds from the open section. At 4 (requests 4, 10, 12 and 14, each at
  station 0), it fails there too (request 4: `[−24327/512, −24325/512]`), so those four are not
  re-entry failures. From the open section 8 of 128 comparisons fail: 6 at station 0 and 2 at
  station 1, the two stations whose lag-2 partner is a request cell.
- In the replay a correct comparison is lost only after a re-entry, in both orders, and removing
  re-entry restores every one. The re-injection explanation holds for 11 of the 15 first wrong locks
  and for every lost comparison of the replay.

## 5. The releases

All 32 releases were released, every lock certified (32 of 32 member certificates a request in the
ordinary release). The open-section tops are the no-re-entry intervention read at every station, not
a release.

| Request | Seed pair | Target | Ordinary release (largest gap) | Clock-order release | Open-section tops |
|---|---|---|---|---|---|
| 0 | 0 0 | 1 1 2 2 3 3 0 0 | 2 1 3 2 3 3 1 0 | **1 1 2 2 3 3 0 0** | **1 1 2 2 3 3 0 0** |
| 1 | 0 1 | 1 2 2 3 3 0 0 1 | 3 2 3 3 1 0 2 1 | 2 2 2 3 3 0 0 1 | 2 2 2 3 3 0 0 1 |
| 2 | 0 2 | 1 3 2 0 3 1 0 2 | 2 3 3 0 0 1 1 2 | 1 3 2 0 3 0 0 1 | **1 3 2 0 3 1 0 2** |
| 3 | 0 3 | 1 0 2 1 3 2 0 3 | 1 3 2 3 3 1 0 1 | 1 2 2 2 3 3 0 0 | **1 0 2 1 3 2 0 3** |
| 4 | 1 0 | 2 1 3 2 0 3 1 0 | 3 1 3 2 3 3 1 0 | 1 2 2 2 3 3 0 0 | 1 1 3 2 0 3 1 0 |
| 5 | 1 1 | 2 2 3 3 0 0 1 1 | 3 2 3 3 1 0 2 1 | 2 2 2 3 3 0 0 1 | **2 2 3 3 0 0 1 1** |
| 6 | 1 2 | 2 3 3 0 0 1 1 2 | **2 3 3 0 0 1 1 2** | 2 2 3 3 0 0 1 1 | **2 3 3 0 0 1 1 2** |
| 7 | 1 3 | 2 0 3 1 0 2 1 3 | 2 3 3 1 0 2 1 3 | 2 2 3 3 0 0 1 1 | **2 0 3 1 0 2 1 3** |
| 8 | 2 0 | 3 1 0 2 1 3 2 0 | 3 1 3 2 3 3 1 0 | 3 1 0 1 1 2 2 2 | **3 1 0 2 1 3 2 0** |
| 9 | 2 1 | 3 2 0 3 1 0 2 1 | 3 2 3 3 1 0 2 1 | **3 2 0 3 1 0 2 1** | 3 1 0 3 1 0 2 1 |
| 10 | 2 2 | 3 3 0 0 1 1 2 2 | 2 3 3 0 0 1 1 2 | 2 2 2 3 1 0 2 1 | 2 2 0 0 1 1 2 2 |
| 11 | 2 3 | 3 0 0 1 1 2 2 3 | 1 0 2 1 1 2 1 3 | 2 0 3 1 0 2 1 3 | 2 0 0 1 1 2 2 3 |
| 12 | 3 0 | 0 1 1 2 2 3 3 0 | 3 1 3 2 3 3 1 0 | 2 1 3 2 0 3 0 0 | 2 1 1 2 2 3 3 0 |
| 13 | 3 1 | 0 2 1 3 2 0 3 1 | 3 2 3 3 1 0 2 1 | 0 2 1 3 2 0 3 0 | **0 2 1 3 2 0 3 1** |
| 14 | 3 2 | 0 3 1 0 2 1 3 2 | 2 3 3 0 2 1 1 2 | 2 2 2 2 2 2 2 2 | 2 3 1 0 2 1 3 2 |
| 15 | 3 3 | 0 0 1 1 2 2 3 3 | 1 0 2 1 1 2 1 3 | 0 0 1 1 2 2 2 3 | **0 0 1 1 2 2 3 3** |

Whole (bold): the ordinary release 1 of 16, the clock-order release 2 of 16, the open-section tops
9 of 16. Re-entry, in either order, costs the whole sections the open section reads.

## 6. The repair the evidence points to [agent-inferred; not built]

The law, in its owner `hnn::prediction::BankPlacement` (the span weights `SourceMoment::phase_weights`
realizes; Lean `HNN/IndexedOpen` §4 at the build): **a candidate at station `j` reads each datum of
the span at its transport distance from `j`, through the two-sided modulus of the dissipative
ring**,

```text
w_k^(j) = ρ^(|τ_j − τ_k|) / Σ_(l∈span) ρ^(|τ_j − τ_l|)
```

The ring's stationary response to a datum decays in both directions of the tube; the one-way
dilation used now grows backward. The consequences, read from the numbers above:
- **On data older than the station read, it is the present law exactly** (the common factor
  `ρ^(7−j)` cancels). The clock-order replay above is therefore this law's reading on the request and
  the past locks, and the open section, which holds only past data, is unchanged.
- **A lock at distance `r` adds `ρ^r ≤ ρ` to station `j`'s mass.** Station 7's lock read from
  station 0 takes `[5/256, 3/128]` of that span, against `[205/256, 103/128]` now, and scales the rest
  by a factor in `[125/128, 251/256]`, against `[25/128, 51/256]`. The far-end-first locks no longer
  quench the earlier stations.
- **The weights are framed by the station read**, no longer frame-free. Each station's normalization
  is its own systolic reduction over the same carried powers `ρ^r`.
- **What it does not repair.** A lag-1 neighbour's amplitude (clock order's 9 of 13) is unchanged,
  and `E`'s key must learn to discount it under the repaired law, in contexts where a lag-1 datum is
  placed. The present fit was fitted only on far-end-first trajectories. This is a finite fit's
  failure; no limit of representation is claimed.

Owed with the build (to #62 then): the station-framed weights' mass, their coincidence with the
one-way law on past data, and the bound `ρ^r` on a lock's added mass.

## 7. Time and memory

| Read | Measured | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| the projection read, 1 request | 58,769 ms | none | 75,522,048 |
| the diagnostic, 16 requests (24 host cores) | 138,067 ms | 250,000–700,000 ms / 900,000 ms | 105,271,296 |
| the float prototype (exterior) | under 2,000 ms | none | 40,738,816 |

The diagnostic ran below its projection's lower end: the 16 requests read as co-present regions kept
the cores fuller than the one-request read did. The float prototype and the native owner agree on the
first loss at 63 of 64 (request, order, storage) cells. The one difference is a denominator-alone
reading below one (request 6, the release's order, station 1). The ordinary releases are equal at 16
of 16.

## 8. Commits and gates

- `4ace967b`: the harness (`bank_causes -- reentry <export> <out>`; `eD_reentry.py`; the export's
  fitted constitution read by one helper shared with `native-release`). No library code changed.
- This record's commit: the record, its receipts, the records route and THE_REBUILD's entry.

Gates: `cargo check --workspace --all-targets` clean. `cargo test -p holonics --lib` was not run,
because no library code changed.

The receipts (`2026-09-30_THE_RE_ENTRY_DIAGNOSTIC_receipts/`, synthetic terrain only): `export.txt`
(the frozen `E` and `ρ` and the 16 requests with the float releases), `trace.txt` (every insertion,
both orders, full and denominator-alone margins with the target's and rival's member growths, the
open section, both releases), `summary.txt` (the run's counts, time and memory) and
`float_prototype.txt`.
