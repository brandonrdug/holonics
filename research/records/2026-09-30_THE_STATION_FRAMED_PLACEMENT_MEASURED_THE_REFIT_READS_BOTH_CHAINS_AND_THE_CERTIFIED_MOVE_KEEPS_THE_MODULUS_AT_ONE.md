# The station-framed placement measured: the refit reads both chains, and the certified move keeps the modulus at one

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
runs under the [pin](2026-09-30_THE_STATION_FRAMED_PLACEMENT_PINNED_BEFORE_ITS_RUNS.md) (`b4c133f0`)
and the slope diagnostic after them; [proved-derived; formal-checked] for Lean `HNN/IndexedOpen` §5;
[proved-derived; implemented-exact] for the owners' laws held by their tests; [agent-inferred] where
marked.

**Occasion.** The [re-entry diagnosis](2026-09-30_THE_RE_ENTRY_DIAGNOSED_A_LATER_LOCK_TAKES_THE_SPANS_MASS_AND_QUENCHES_THE_EARLIER_STATIONS.md)
located the passage law's blocker in `BankPlacement`'s normalization and stated the repair: a
candidate at station `j` reads the span as a field, each datum at its two-sided transport distance
from `j`. It was built in its owner (`fb871bb5`), derived and pinned (`b4c133f0`), and run once.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches the tube (the
request and its section one span, read as the pairing of the station's section with each datum's),
the helix (the placed phases), the cell holonomy (the bank's monodromy over the turn) and faces and
placement (each datum's weight); the pair and the tower thread stay attached.

## 0. The recorded failures this work could repeat, and how each was held

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **2, a window or an index of contexts.** The two-sided decay is not a neighbourhood window: every
  datum of the span enters with positive weight at every modulus (Lean `framed_weight_pos`), none is
  dropped by distance or length, and no pair table or lag is read. The only learned scalar is `ρ`.
- **4, a located cause carried unrepaired.** The one-way normalization is repaired in its owner and
  every consumer moved in the same commit; the readout's one anchor, which cannot read a
  station-framed span, is refused below modulus one where a lock follows an open station, not left
  on the old law. The cause this record locates (§7) is named for the next loop; no new consumer is
  built on it.
- **6, seen material graded as unseen.** The seed test re-reads Stage 0's held-out requests for
  comparability and claims no transfer; the float fit read them for its progress lines, as the
  passage law's did, and its last `E`, not a best one, was exported. The confirmation seeds
  `2_026_093_011`–`016` were read by no run before the pin; they were read once each.
- **7, a local pass read as progress.** The seed test's 96 whole sections are a float fit read
  natively on requests the fit's progress lines read; the confirmation, which the native certified
  training reaches from the opening, is 0 whole, and this record reports both as they are.
- **9, a refusal answered with a larger limit.** Every run inside its pinned projection; nothing
  rerun, no guard suspended (the outer process guards held at 100 seconds past each deadline).
- **11, the programming language.** The law is stated as a tube's pairing read from a station, a
  transport's modulus and the distance between two ticks.

## 1. The law

A candidate at station `j` reads the request and the placed section as one joint field, each datum at
its two-sided transport distance from `j`:

```text
w_j(k) = ρ^|τ_j − τ_k| / Σ_(l∈span) ρ^|τ_j − τ_l|       (Lean framedWeight; BankPlacement::{weights, storage})
```

Lean `HNN/IndexedOpen` §5 (9 theorems, standard axioms only): unit mass and positive weight for every
datum (`framed_weight_mass`, `framed_weight_pos`); on data no later than `j`, the one-way law read at
any later frame (`framed_weight_one_sided`); a datum `r` ticks away on either side weighs `ρ^r` times
the candidate and at most `ρ^r` (`framed_weight_ratio`, `framed_weight_le_pow`); the one-way law's
backward growth `ρ^(−r)` (`oneway_later_weight_ratio`); symmetry, translation and the lossless case.
The executed comparison's pullback and certified move keep their form, each contribution read from
its own station (the owner's pullback identity exact at `ρ = 1` and `3/4`). `ρ` stays the learned
passive locus.

**The modality statement.** The law reads only the distance between two ticks of the ring's clock:
a text cell, a pixel at its scan tick (its row neighbours one tick away on either side, weighing
alike; the pixels a row away at the row's width `w`, weighing `ρ^w` on either side), an audio sample
at its sample tick, a screw at its step. A second ring whose clock advances by rows carries the
transverse distance by the same law.

## 2. The seed test (pinned item 2)

**2a, the acceptance.** The probe fit `E` and `ρ` on the release's own trajectory from the opening
under the new law (`eO_fit.py order2 400 256 101 0.03 0.05 1 16`, float, 1,086,233 ms); the last
`E` and `ρ` exported and read natively on Stage 0's 128 held-out requests, both rounded to the source
port's lattice (`ρ = 137573/262144`, between `67/128` and `135/256`; `E`'s largest entry
`2717237/1048576`, between 2 and 3, against the bound 8).

| Reading | 2a: the refit, native | 2b: the frozen passage-law fit, native, new law | The passage law (its fit) | Stage 0 (the one-population law) |
|---|---|---|---|---|
| released / held / refused | 128 / 0 / 0 | 128 / 0 / 0 | 128 / 0 / 0 | 128 / 0 / 0 |
| **whole sections equal to their targets** | **96** of 128 | 11 | 9 | 17 |
| first lock at station 0 or 1 | 0 | 0 | 0 | 44 |
| **first lock right** | **128** of 128 | 128 | 128 | 57 |
| sections following the rule among their own stations | 106 | 19 | 17 | 97 |
| stations right (of 1,024) | 917 | 677 | 677 | 404 |
| stations right, by station | 113 126 103 126 99 126 99 125 | 71 106 66 111 54 105 54 110 | 56 118 58 104 56 111 54 120 | 52 50 50 52 50 50 47 53 |
| native and float releases agree | 1,024 of 1,024 | 663 of 1,024 (its float column is the one-way law's release) | 1,024 | 1,024 |
| teacher-forced tops right | 1,007 of 1,024 | 833 (the one-way law's: past data only) | 833 | 869 |
| members certified; executed ticks closed | 4,096 of 4,096; 245,760 of 245,760 | the same | the same | the same |
| candidate crossings past the signed form | 0 of 23,040 | 0 of 23,040 | 0 | 0 |
| the transport modulus | `137573/262144` | `1452225/2097152` | `1452225/2097152` | 1 |

**Item 2 improves**: 96 whole sections exceed 17, and the first lock is right at 128 of 128, more
than 57. The first lock is never at station 0 or 1 (station 5 at 61 requests, 3 at 46, 4 at 17, 7
at 4), each right. **Both chains are read**: the even stations (the chain seeded by `x_38`) imply
`x_38` (or a seed equal to both last cells) at 414 of 512 decisions (the passage law: 224), the odd
stations `x_39` (or both) at 503 of 512 (453). The frozen fit gains 2 whole sections from the
placement alone (11 against 9): its readings after the first lock were fitted under the one-way law,
where the far lock dominated; the refit learns under the law it is read by, and its `ρ` fell to about
one half (between `4/5` and `5/6` at step 50, below `7/10` by step 100, below `3/5` by step 150).

**The synthetic outputs of 2a** (the first 16 of 128; all 128 with their locks, readings and
certificates in the receipts):

| Request | Last four request cells | Target | Released | Lock order |
|---|---|---|---|---|
| 0 | 0 2 1 1 | 2 2 3 3 0 0 1 1 | 2 2 3 3 0 0 1 1 (whole) | 5 7 3 1 4 6 2 0 |
| 1 | 2 0 2 0 | 3 1 0 2 1 3 2 0 | 3 1 0 2 1 3 2 0 (whole) | 5 7 3 1 2 4 6 0 |
| 2 | 1 2 3 2 | 0 3 1 0 2 1 3 2 | 0 3 1 0 2 1 3 2 (whole) | 4 6 2 0 7 3 5 1 |
| 3 | 0 1 2 2 | 3 3 0 0 1 1 2 2 | 3 3 0 0 1 1 2 2 (whole) | 3 5 7 1 6 4 2 0 |
| 4 | 0 3 0 2 | 1 3 2 0 3 1 0 2 | 1 3 2 0 3 1 0 2 (whole) | 3 5 7 1 0 2 6 4 |
| 5 | 1 1 0 3 | 1 0 2 1 3 2 0 3 | 3 0 0 1 1 2 2 3 | 5 7 3 1 2 4 6 0 |
| 6 | 3 0 0 2 | 1 3 2 0 3 1 0 2 | 1 3 2 0 3 1 0 2 (whole) | 4 6 2 0 7 1 3 5 |
| 7 | 1 2 1 2 | 2 3 3 0 0 1 1 2 | 2 3 3 0 0 1 1 2 (whole) | 3 5 7 1 0 2 4 6 |
| 8 | 3 0 2 3 | 3 0 0 1 1 2 2 3 | 3 0 0 1 0 2 1 3 | 5 7 3 1 4 6 2 0 |
| 9 | 3 1 1 3 | 2 0 3 1 0 2 1 3 | 2 0 3 1 0 2 1 3 (whole) | 5 7 3 1 0 4 6 2 |
| 10 | 3 0 1 3 | 2 0 3 1 0 2 1 3 | 2 0 3 1 0 2 1 3 (whole) | 7 5 3 1 0 4 6 2 |
| 11 | 2 2 3 2 | 0 3 1 0 2 1 3 2 | 0 3 1 0 2 1 3 2 (whole) | 4 6 2 0 7 3 5 1 |
| 12 | 3 0 1 2 | 2 3 3 0 0 1 1 2 | 2 3 3 0 0 1 1 2 (whole) | 4 6 2 7 5 0 3 1 |
| 13 | 0 3 2 0 | 3 1 0 2 1 3 2 0 | 3 1 0 2 1 3 2 0 (whole) | 5 7 3 1 2 4 6 0 |
| 14 | 0 0 3 1 | 0 2 1 3 2 0 3 1 | 0 2 1 3 2 0 3 1 (whole) | 5 7 3 1 0 2 4 6 |
| 15 | 3 2 1 2 | 2 3 3 0 0 1 1 2 | 2 3 3 0 0 1 1 2 (whole) | 3 5 7 1 4 6 2 0 |

The release still locks one chain first, far end first, and then the other; what changed is that the
other chain now reads its own seed through the locked chain. The two wrong rows show the secondary
cause: request 5's even stations copy the odd station one tick before each (`3 0 0 1 1 2 2 3`), the
lag-1 neighbour read in place of the seed, and request 8's even chain is right at stations 0 and 2
and one class behind at 4 and 6.

## 3. The re-entry diagnostic, re-read (items 2c and 2d)

**2c: the frozen fit, the same 16 development requests, under the new law** (`bank_causes -- reentry`
on the diagnosis's export, 137,327 ms). In clock order every count equals the diagnosis's, as the law
requires (every placed datum precedes the open stations: `framed_weight_one_sided`). In the release's
own order:

| The release's own order | The one-way law (the diagnosis) | The station-framed law |
|---|---|---|
| comparisons holding by insertion, full | 120/128 71/112 47/96 32/80 15/64 11/48 8/32 9/16 | 120/128 87/112 62/96 34/80 21/64 21/48 15/32 6/16 |
| the same, the denominator alone | 120/128 39/112 17/96 16/80 14/64 10/48 5/32 2/16 | 120/128 92/112 66/96 46/80 29/64 16/48 8/32 4/16 |
| open targets past one, the denominator alone, at insertions 1 and 4 | 34 of 112; 2 of 64 | 112 of 112; 44 of 64 |
| the first loss, by insertion 1..7 (full) | 15 0 0 0 0 0 0, never 1 | 14 1 1 0 0 0 0, never 0 |
| the first lost comparisons | 35 | 21 |
| by distance to the nearest placed lock, 1 / 3 / 5 / 6 / 7 | 10 / 12 / 10 / 0 / 3 | 10 / 8 / 1 / 1 / 1 |
| of those, lost by the denominator alone | 28 | 10 (8 of them at distance 1) |
| the ordinary release, whole | 1 of 16 | 2 of 16 |

**Where the first lost comparison now falls**: still at the first insertion (14 of 16 requests), but
at the placed lock's neighbours: of 21 first losses, 10 lie one tick from the lock and 8 three ticks
away, 3 farther; 20 of the 21 at an odd distance, the other chain's data. The far stations' quench
is gone: losses at five ticks or more fell from 13 to 3, and the enlarged denominator no longer
drives any open target below one at the first insertion (112 of 112 past one, against 34). What the
denominator alone still does, it does at one tick (8 of its 10 losses), where a lock weighs `ρ`
times the candidate, by the law.

**2d: the refit on the same 16 development requests** (the diagnostic on 2a's `E` and `ρ`, 135,084
ms): the ordinary release is whole at 11 of 16 and the clock-order release at 12; the refit's own
open-section tops are whole at 11 (the frozen fit: 2, 2 and 9), 8 of them on the same requests as
the ordinary release, so the lock iteration's re-entry completes three sections the open section
misses and breaks three it reads. The first loss still comes at the first insertion (15 of 16): 26
comparisons, 19 one tick from the lock and 7 three ticks away, 20 of the 26 also lost by the
denominator alone. They are losses against the open section's reading: under the full placement
every open target stays past one at every insertion, and the comparisons return as the rest is
placed (holding by insertion 122/128 85/112 73/96 54/80 34/64 39/48 29/32 16/16).

The float prototype (`eD_reentry.py`) and the native owner agree on the first loss at every one of
the 64 (request, order, storage) cells of the frozen fit.

## 4. The confirmation and the regressions (pinned item 3)

Item 2 improved, so the certified executed comparison trained `E` and `ρ` from the declared opening
along the machine's own open-section trajectory, and every constitution generated 128 fresh
requests at its unread confirmation seed.

**Training** (each batch read at `E` before its move, a fresh batch every move):

| Terrain, seed | Moves adopted / refused | First batch: before → after (nats) | Last batch: before → after | The modulus | Wall ms |
|---|---|---|---|---|---|
| order-2, `2_026_093_011`, 16 of 8 | 16 / 0 | `[322608, 322612)/4096` → `[203101, 203114)/4096` | `[16602, 16622)/4096` → `[11942, 11963)/4096` | 1 at every move | 1,359,138 |
| alternation, `2_026_093_013`, 8 of 8 | 8 / 0 | `[340232, 340235)/4096` → `[227119, 227127)/4096` | `[210458, 210468)/4096` → `[205336, 205347)/4096` | 1 at every move | 689,183 |
| line, `2_026_093_015`, 8 of 8 | 8 / 0 | `[338346, 338350)/4096` → `[109173, 109181)/4096` | `[76539, 76553)/4096` → `[75365, 75378)/4096` | 1 → `2002021/2097152` (from move 3; between `61/64` and `31/32`) | 1,051,440 |

Every adopted move held every guard. On order-2 the comparison fell on every fresh batch, from
between 78 and 79 nats at the first to between 4 and 5 at the last, while the training batches'
releases stayed at no whole section and at most 21 of 64 stations right.

**Confirmation** (128 requests each at the unread seeds; every constitution from the open section):

| Terrain | Constitution | Released / held / refused | Whole sections | Incorrect releases | Reaching the termination | Stations right (of 1,024) | By station | First lock at station 0 or 1 (of them right) |
|---|---|---|---|---|---|---|---|---|
| order-2 (`…012`) | the opening | 0 / 128 / 0 | **0** | 0 | 35 | 239 | 36 27 32 21 28 28 27 40 | 0 (0) |
| order-2 | `executed-open` | 128 / 0 / 0 | **0** | 128 | 0 | 240 | 21 32 31 47 23 34 30 22 | 17 (5) |
| alternation (`…014`) | the opening | 12 / 116 / 0 | 12 | 0 | 0 | 358 | 55 43 48 56 42 32 42 40 | 0 (0) |
| alternation | `executed-open` | 100 / 28 / 0 | **19** | 81 | 29 | 366 | 47 55 54 55 47 35 38 35 | 33 (12) |
| line (`…016`) | the opening | 9 / 119 / 0 | 9 | 0 | 33 | 297 | 25 34 37 43 25 41 40 52 | 0 (0) |
| line | `executed-open` | 60 / 68 / 0 | **15** | 45 | 0 | 311 | 31 45 50 43 37 33 38 34 | 27 (6) |

No refused certificate in any release. **The order-2 confirmation fails its acceptance** (0 whole
sections against the opening's 0; stations at a quarter, 240 of 1,024). **Both regressions pass**
(19 against 12 and 15 against 9 whole sections).

**The synthetic outputs** (order-2, the trained constitution, the first 16 of 128; every section of
every confirmation in the receipts):

| Last four request cells | Target | Released | Lock order |
|---|---|---|---|
| 1 1 1 2 | 2 3 3 0 0 1 1 2 | 3 1 1 3 1 1 3 3 | 7 6 1 2 5 3 0 4 |
| 2 0 3 3 | 0 0 1 1 2 2 3 3 | 3 3 2 2 3 3 0 2 | 5 3 2 0 7 4 1 6 |
| 3 3 3 1 | 0 2 1 3 2 0 3 1 | 3 3 1 1 1 1 1 1 | 2 3 1 5 0 6 7 4 |
| 1 2 3 3 | 0 0 1 1 2 2 3 3 | 1 3 3 1 1 1 1 1 | 0 4 3 2 5 1 6 7 |
| 2 1 2 1 | 3 2 0 3 1 0 2 1 | 3 3 3 1 2 3 3 1 | 3 5 2 7 6 0 4 1 |
| 1 1 2 0 | 3 1 0 2 1 3 2 0 | 2 0 1 2 3 3 1 3 | 4 7 5 2 6 0 1 3 |
| 2 3 1 0 | 2 1 3 2 0 3 1 0 | 3 3 2 1 1 1 2 3 | 2 6 7 4 0 3 1 5 |
| 1 1 0 2 | 1 3 2 0 3 1 0 2 | 3 1 1 0 3 1 1 3 | 7 4 1 0 2 5 3 6 |
| 1 2 2 2 | 3 3 0 0 1 1 2 2 | 2 3 2 0 2 1 2 3 | 7 0 4 2 5 1 3 6 |
| 3 3 1 3 | 2 0 3 1 0 2 1 3 | 0 1 1 0 1 1 1 1 | 0 6 2 5 1 4 7 3 |
| 2 1 1 0 | 2 1 3 2 0 3 1 0 | 3 3 1 0 3 3 2 3 | 7 4 2 1 3 0 6 5 |
| 0 3 1 0 | 2 1 3 2 0 3 1 0 | 3 1 0 3 1 1 0 2 | 1 5 4 7 0 2 6 3 |
| 3 0 3 2 | 0 3 1 0 2 1 3 2 | 0 1 1 0 0 1 1 2 | 6 2 5 1 0 7 3 4 |
| 1 2 1 0 | 2 1 3 2 0 3 1 0 | 1 3 3 2 1 1 1 1 | 3 4 0 7 2 6 1 5 |
| 1 2 3 1 | 0 2 1 3 2 0 3 1 | 2 3 3 0 0 1 3 2 | 6 0 2 7 5 1 4 3 |
| 3 1 1 3 | 2 0 3 1 0 2 1 3 | 3 1 2 3 3 3 2 2 | 4 5 2 0 1 7 3 6 |

No released section follows the rule; the opening held all 128.

## 5. The falsifiers, read as written

- **The native owner and the float probe disagree on the new law: does not fire.** 1,024 of 1,024
  stations in 2a; the first loss at 64 of 64 cells in 2c.
- **The enlarged denominator alone still reproduces most first losses in the release's own order:
  does not fire.** 10 of 21 (against 28 of 35 under the one-way law), 8 of them one tick from the
  lock, where the law weighs a lock `ρ` times the candidate.
- **The seed test does not improve: does not fire.** 96 whole sections against 17; the first lock
  right 128 against 57.
- **Training improves and untouched confirmation does not: fires on order-2.** The certified
  training's comparison fell on every fresh batch (from `[322608, 322612)/4096` to
  `[16602, 16622)/4096` nats at its first reading), and on the confirmation it released 0 whole
  sections, as the opening's 0. It does not fire on the alternation or the line.
- **A resource bound is reached: does not fire** (§8).

## 6. The verdict

- **Built and exact**: the station-framed law in `BankPlacement`, every consumer moved, the readout's
  one anchor refused where it cannot read the law, Lean `HNN/IndexedOpen` §5 (9 theorems).
- **Acceptance 1 holds** (every read release certified, every adopted move within its guards, the
  gates of §9); **acceptance 2 holds**: the refit under the new law releases 96 whole sections of 128
  from the open section with every first lock right, against 17 and 9; **acceptance 3 fails** on
  order-2 (0 against 0 whole sections) and holds on both regressions; **acceptance 4 holds**.
- The re-entry is repaired where the diagnosis located it: in the release's own order the far lock no
  longer quenches the earlier stations; what remains is the other chain one and three ticks away,
  which the refit reads through (11 of 16 whole on the development requests, as many as its own
  open-section tops).

## 7. What the measurement located [measured; agent-inferred where marked]

**The certified move does not take the modulus below one on order-2.** In 16 moves of the pinned
training and 8 of the alternation's the modulus stayed at one, where the station-framed law is the
one population in every frame (`framed_weight_lossless`): the native training never read what the new
law adds. On the line it did leave one (to between `61/64` and `31/32` from the fourth move). A
diagnostic after the pinned runs (the harness now prints the move's two slopes; `executed train
executed-open order2 41 8 3`, development seed 41, 74,259 ms) reads the modulus's slope
`γ_ρ = Σ sign ⟨ĝ, ∂z/∂ρ⟩` on each move from the opening: `[−645906, −645905)/4096`,
`[−959949, −959948)/4096` and `[−6738, −6737)/4096`, all negative, beside the port's first-order
slopes `[−2873630, −2873629)/4096`, `[−653220, −653219)/4096` and `[−1462480, −1462479)/4096`.
A negative `γ_ρ` means the release's comparison at the opening descends by raising the modulus, past
the passive bound, so the move holds it at one. The float fit, descending the softmax of the executed
log-growths on the same trajectory, took `ρ` below `7/10` within 100 steps, and there the rule is
read (its 96 whole sections).

**The blocker, by its measurement**: from the declared opening the executed comparison's slope in
the transport modulus is negative at `ρ = 1` on every order-2 move read, so its certified move keeps
the transport lossless, where no reading marks the span's frontier (`lossless_term_modulus`), and 16
moves release 0 whole sections of 128. Which terms carry the negative slope is not yet read: at the
opening nothing is past one (it held all 128 confirmation requests), so the threshold terms are
positive at every station, and the float fit's softmax compares the candidates with one another
only. [agent-inferred] The experiment that tells is `γ_ρ` split by term kind (threshold against
class) on the opening's batches and on the fitted `E`. This is the next loop's subject, in its owner
(`hnn::executed`, the modulus's part of the committed move), before any further consumer.

## 8. Time and memory

| Run | Measured ms | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| 2a fit (float, 400 steps) | 1,086,233 | 1,000,000–1,600,000 / 2,400,000 | 191,139,840 |
| 2a native read, 128 | 487,271 | 400,000–600,000 / 900,000 | 130,412,544 |
| 2b native read, 128 | 469,410 | 400,000–600,000 / 900,000 | 129,081,344 |
| 2c re-entry, 16 | 138,002 | 100,000–300,000 / 900,000 | 105,893,888 |
| 2d re-entry, 16 | 135,753 | 100,000–300,000 / 900,000 | 106,008,576 |
| order-2 training, 16 moves | 1,359,138 | 200,000–3,000,000 / 3,600,000 | 247,373,824 (sampled) |
| order-2 confirmation, 2 × 128 | 482,551 | 100,000–700,000 / 1,200,000 | 115,535,872 |
| alternation training, 8 moves | 689,183 | 100,000–1,800,000 / 2,400,000 | 227,450,880 (sampled) |
| alternation confirmation | 364,668 | 100,000–700,000 / 1,200,000 | 110,940,160 |
| line training, 8 moves | 1,051,440 | 100,000–1,800,000 / 2,400,000 | 223,567,872 |
| line confirmation | 337,314 | 100,000–700,000 / 1,200,000 | 117,784,576 |
| the slope diagnostic, 3 moves (not pinned) | 74,259 | none | 176,062,464 |

Every run within its projection and deadline, one at a time; the float prototypes of 2c and 2d under
2,000 ms each.

## 9. Owed in #62

"The station-framed placement" (September 30; `hnn::prediction::BankPlacement`; Lean
`HNN/IndexedOpen` §5 proves the framed weights' mass, positivity, one-sidedness on older data, ratio,
bound, symmetry, translation and the lossless case, and the one-way law's backward growth):
1. **The framed derivative**: `∂_ρ w_j(k) = w_j(k)(r_k − r̄)/ρ` as a `HasDerivAt` statement on
   `0 < ρ`, the owner's `modulus_derivative` its instance (held by the test to second order).
2. **The stationary two-sided kernel**: that `ρ^|Δ|` is the stationary response of a first-order
   dissipative transport of modulus `ρ` a tick read in both directions of the tube (its pairing
   reading), on the tube's owner (`Transport/ContinuingTube`).
3. **The phases' distances**: within one turn a datum counted at phase `c` lies
   `1 + j + ((τ − c) mod d)` ticks before station `j` (held on instances by the owner's tests).
4. **The readout's station-framed form**: one anchor per frame, or a reading that carries the frame
   through the refinement; until then refused below modulus one.
5. **The modulus's move at the passive bound**: the committed move's first-order certificate for `ρ`
   at `ρ = 1` when `γ_ρ < 0` (the bound active), and what the release's comparison must read for its
   slope in `ρ` to point inward.

## 10. Commits and gates

- `fb871bb5`: the law in its owners, Lean `HNN/IndexedOpen` §5, the tests, the probe and harnesses,
  the atlas rows.
- `b4c133f0`: the pin.
- This record's commit: the record, its receipts (synthetic terrain only), the counting scripts
  (`bank_causes_probe/eF_{release_counts, reentry_distances, confirmation_counts}.py`), the training
  harness's slope line, the records route, the atlas owner and THE_REBUILD's entry.

Gates at `fb871bb5`, unchanged since in the library and the Lean: `cargo check --workspace
--all-targets` clean; `cargo test -p holonics --lib` 974 passed; `bash tools/lean_check.sh Holonics
HolonicsResearch` 10,251 jobs, no `sorry`. The card suite (`holonics-cuda`) was not run from the
isolated worktree; the card crate did not change, and at modulus one, the only modulus the card
accepts, the new law is the old one. The primary runs it after the merge.

The receipts (`2026-09-30_THE_STATION_FRAMED_PLACEMENT_receipts/`): the fit's log and export, both
native traces and their counts, both re-entry traces with summaries, distances and float prototypes,
every training log and trained `E`, every confirmation's counts and sections, and the slope
diagnostic.
