# Loop 1c, c2: normalization alone undoes two of three losses, one is an interaction, and the entry keeps the four retained

**Date.** October 1. **Issues.** #73, #63. **Grade.** [measured]. One bounded diagnostic, cleared by
GPT-6 Astra with Brandon's approval and run once. It is diagnostic only: no law changes and no learning
claim is made.

**Pin.** [Loop 1c's pin](2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md),
narrowed under Astra's reviews to this one operation. The long replay and the fit are withdrawn
because neither would change the next decision. Receipts are in
[`2026-10-01_LOOP_1C_receipts/c2/`](2026-10-01_LOOP_1C_receipts/c2/): the listing, the error stream, the
timing, the check's diff, c2's complete continuing state, its native release's contexts, and the
identities.

## The operation and its identities

- **Steps.** Gate A's saved constitution 1 was restored whole, and one native update was taken
  through `hnn::executed::executed_move` on gate A's move-1 batch. Constitution 2 and its contexts
  were captured, and then the seven re-reads at c2 were read: the decisions solved at their own
  lock that later locks followed. Native order only.
- **Identities.**
  - Source: main `117b79a5`.
  - Binary sha256: `11d947689a3b840de7dfc570c318f7bc80c68db47c7985a0d1729cd1cf54c016`.
  - Restored state sha256: `697ecec94d86e4abf242e8e1541cabe176b1d70c75c360cd3bb399d58f3e3073`, written
    back identical to its file.
- **Reproduction.** Constitution 1's reading, move 1's line and constitution 2's reading all equal
  gate A's receipt. c2's persistence equals gate A's move-2 line: `solved 7, reread 7, stay 4,
  fall 3`. The three losses are `reversed 3`, which is proved, with `uncertified 0` and no refused
  read.
- **Time.** The move took 168,004 ms of its 210,496 ms bound. The reads at c2 took 844 ms: 105
  candidate turns, with 35 more kept from the move's own reading. The whole run took 168,889 ms
  against an outer guard of 257 s. No guard fired.

## The factorial

The four cells are `(N0D0, N1D0, N0D1, N1D1)`.
- `N` is the later locks' change to the span's normalization.
- `D` is the later data's entry into the station's reading.
- `N1D1` is the actual release; `N0D0` is the decision as read at its own lock.

`H` means solved and `F` means a proved failure. The solved level is `ℓ < ln 2`, with `ln 2` between
`45,426/65,536` and `45,427/65,536`.

| Re-read | Target | Later locks' classes | Native | Pattern |
|---|---|---|---|---|
| request 0, station 6 | 1 | 1, 1, 2, 2, 2, 0 | lost (reversed) | H F H F |
| request 1, station 5 | 1 | 1, 0, 0, 0, 1, 1 | lost (reversed) | H F H F |
| request 7, station 7 | 1 | 1, 2, 2, 2, 0 | lost (reversed) | **H H H F** |
| request 2, station 4 | 1 | 1, 2, 1, 0, 0 | retained | H F H H |
| request 4, station 6 | 3 | 3, 3, 3, 3, 3, 3 | retained | H F H H |
| request 4, station 1 | 3 | 3 | retained | H F H H |
| request 5, station 4 | 3 | 3, 3, 3, 3 | retained | H F H H |

- **Two of the three losses (H F H F)** come from the normalization. Applied alone it undoes them,
  the entry alone does not, and both together undo them. Both telescoping orders charge the loss to
  the normalization.
- **One loss (request 7, station 7: H H H F) is a pure interaction.** Neither factor undoes it alone;
  only together do they. Its telescoping orders disagree. Normalization first and then entry gives
  `ℓ` from `[27118, 27119)` to `[12466, 12469)` (`/65536`), and the loss lands on the entry. Entry first
  and then normalization gives `[15177, 15179)` to `[24407, 24409)`, and the loss lands on the
  normalization. The interaction lies in `[−2712, −2709)/65536`. The record names no unique cause.
- **All four retained decisions (H F H H)** would be undone by the normalization alone, and the
  entry compensates. Three of them are class-3 targets whose later locks are class 3 too. The fourth
  (request 2, station 4) keeps its decision under mixed later classes.

## Against the outcomes stated before the run

The pre-run statement held that if any lost case has normalization alone holding while it fails
under both, the blanket normalization explanation is rejected. **It is rejected.**
- Request 7, station 7 is that counterexample.
- The normalization carries two of the three losses, and it would undo all four retained decisions
  if the entry did not compensate.
- At the untrained opening (development seed 062) it was implicated in all five losses.

[measured] The factorial's cell `N0D1` is the frozen-denominator reading: the later data enter, and
the normalization is held at the decision's own lock. It holds at c2 in **all seven** re-reads, both
the lost and the retained. At the opening it held in three of the six. So a decided station read
under its own lock's normalization keeps every c2 decision, though not every opening decision. These
are the per-decision readings only. How a frozen denominator would change the release as a whole
(later locks, whole sections) is not read here.

## What it motivates, and what it does not

- It motivates one diagnostic arm on the retained states: a release in which each decided station
  is read under the span's normalization at its own lock, at c2 (the state is now captured) and at
  the opening. It would read whole sections, stations right, and the persistence statuses against
  the native release. Pinned and reviewed before any run, it stays a diagnostic and never becomes
  the production law silently. The interaction case is its control.
- It does not show that no per-station objective can make sections whole, that any representation is
  impossible, or that the learned state is durable. Native continual learning was not tested.
- No escalation was run.

## Corrected after Astra's review of this receipt (October 1)

Two points of the reading above are corrected. They govern over the statements they amend.

1. **Request 7, station 7 is a joint-only threshold crossing, not a pure interaction.**
   - Neither factor alone crosses the solved level. Their additive counterfactual,
     `ℓ10 + ℓ01 − ℓ00`, already lies in `[55021, 55025)/65536`, above `ln 2`'s upper
     `45427/65536`.
   - The nonadditive interaction, `[−2712, −2709)/65536`, is negative: it reduces the loss and is not
     its cause.
   - The blanket normalization explanation stays rejected, because normalization alone holds there.
     "Pure interaction" is withdrawn.
2. **Re-reading a decided station has no behavioural consumer.**
   - The release reads only unlocked stations, commits each lock's class, and derives the section
     from those assignments.
   - Persistence is receipt data. It is formed after the proposal and is consumed by no release or
     update.
   - So a decided station's later re-reading, frozen-denominator or not, changes no release decision:
     whole sections stay 0 of 8, stations right 15, releases 8.
   - The `N0D1` cells above already give that reporting result, and no run is needed for it.
   - The frozen-denominator arm proposed in "What it motivates" is withdrawn as a behavioural test.

**What follows.** The persistence losses do not explain why no section is whole. The causal consumer
is the decision at its own lock: at gate A's best constitution, 7 of 64 decision terms were solved
there. A behavioural counterfactual must be prospective. At a native prefix, for the unlocked
stations, it would compare the current normalization with a declared predecessor-occupancy
normalization, recomputed under the current source port, transport modulus and population chart,
and read every candidate the next selection and certification need. Such an intervention is
constitutive, and is neither a missing coordinate transport nor a law. It is not run here.
