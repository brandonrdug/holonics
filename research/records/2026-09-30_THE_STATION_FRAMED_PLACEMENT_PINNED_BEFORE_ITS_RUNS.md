# The station-framed placement: a candidate reads the span from its own station (pinned before its runs)

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the law's choice and the pins; [proved-derived; formal-checked] for Lean
`HNN/IndexedOpen` §5; [proved-derived; implemented-exact] for the owners' laws held by their tests;
[measured] for the development read (§4), which used development seed 41 only.

**Occasion.** The [re-entry diagnosis](2026-09-30_THE_RE_ENTRY_DIAGNOSED_A_LATER_LOCK_TAKES_THE_SPANS_MASS_AND_QUENCHES_THE_EARLIER_STATIONS.md)
located the passage law's blocker in the release's own order: the damage is normalization.
`BankPlacement` weighed each datum by its age at the span's common end, so a lock `r` ticks after
the station read weighed `ρ^(−r)` times that station's own candidate: read from station 0, station
7's lock took `[205/256, 103/128]` of the span, 34 of 112 targets stayed past one at the first
insertion, and the enlarged denominator alone reproduced 28 of the 35 first losses. Clock order did
not rescue it; the lag-1 neighbour's amplitude is a smaller, secondary cause. §6 there stated the
repair. This record derives it, states what is built (`fb871bb5`) and pins the test before any
measured run.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches four: **the
tube** (the request and its section one span, read as a pairing of the station's section with each
datum's), **the helix** (the placed phases `P^(λ − c)`, unchanged), **the cell holonomy** (the bank's
monodromy over the turn, read on the new storage), **faces and placement** (each datum's weight, the
object changed). The pair (each crossing's contact with the ring) and the tower thread stay
attached: nothing here changes a contact or a restriction.

## 0. The recorded failures this work could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **2, a window or an index of contexts.** A two-sided decay read from the station could turn into
  a neighbourhood window. It does not: every datum of the span enters with positive weight at every
  modulus (Lean `framed_weight_pos`), none is dropped or truncated by its distance or by the span's
  length, no table of pair offsets or lags is read, and the only scalar is the learned modulus `ρ`,
  one at the founding.
- **4, a located cause carried unrepaired.** The located cause (the one-way normalization) is
  repaired in its owner, `BankPlacement`, and every consumer moves with it in the same commit:
  `bank_release`, the executed comparison's returns, its modulus slope, its storage moves and its
  pairing receipt, the face path's admission, the harnesses and the probe. The readout path's one
  anchor cannot read a station-framed span; below modulus one it is refused, typed
  (`HnnError::UnframedAnchor`), where a placed datum follows an open station, not left on the old
  law. The secondary cause the diagnosis named (the lag-1 neighbour's amplitude) is not repaired
  here and is named as the expected blocker (§5).
- **6, seen material graded as unseen.** The seed test re-reads Stage 0's held-out requests for
  comparability and claims no transfer. The confirmation seeds `2_026_093_011`–`016` were read by no
  run (the passage law's confirmation did not run); they are read only if item 2 improves.
- **7, a local pass read as progress.** The acceptance is whole sections and first-lock
  correctness; the open section's tops and the comparisons' margins are reported beside it, never
  as success.
- **9, a refusal answered with a larger limit.** Every run is projected and pinned with its
  deadline (§4); a run that reaches it is reported incomplete and not rerun; no guard is suspended.
- **1 and 5, an authored routine; no catered machinery.** Nothing names the order-2 rule, a lag or
  a chain; the terrain alone computes truth. The distance is read from the ring's clock, the one
  object every modality has.
- **5, an uncertified deposition step.** The certified move is unchanged: every guard a commit
  guard, the modulus's slope read from each contribution's station.
- **11, the programming language.** The law is a tube's pairing read from a station: a transport's
  modulus, the distance between two ticks of a clock, a span's mass read from the station. Arrays of
  weights are its realization.

## 1. The law, derived

**The one-way law and why it failed.** The passage law read every datum at `ρ^(a_k)`, `a_k` its
age at the span's end `e`: the retarded transport of a dissipative navigator, the modulus a datum
keeps after travelling forward to the end. The ratio of two data's weights is frame-free only
while the frame lies at or after both (`decayed_weight_frame_free`); read at the end, a datum `i`
crossing `r` ticks before `k` weighs `ρ^r` times `k` (Lean `oneway_later_weight_ratio`). So a lock
`r` ticks after the station read weighs `ρ^(−r)` times the station's own candidate: the transport's
dilation grows backward from the station. The release's own order locks the far end first (from
the open section a far station's candidate is the heaviest datum of its span), so under the one-way
law each far lock took the mass of every earlier station's span.

**The section is a joint field** (CLAUDE.md, "Generation and action": generation refines a joint
field and releases its boundary, not a sequence of tokens). A candidate at station `j` is read with
the whole span placed on the ring at once, not after the data in time order. The tube's pairing
reading (the winding guide §5: a tube is one object with a map reading and a pairing reading) of a
dissipative transport of modulus `ρ` a tick, read at station `j`, is the stationary response to a
datum `k`, which falls by `ρ` a tick in both directions: `ρ^|τ_j − τ_k|` (the stationary kernel of a
first-order transport of modulus `ρ`, symmetric in the two directions of the tube). Read over the
span's mass from `j`:

```text
w_j(k) = ρ^|τ_j − τ_k| / Σ_(l∈span) ρ^|τ_j − τ_l|                     (Lean framedWeight)
r_j(c) = 1 + j + ((τ − c) mod d)   a request phase c,   r_j(i) = |i − j|   a placed station i
z_j(S) = z_pairs + Σ_c w_j(c) P^(λ−c) E M[c] + Σ_(i∈S) w_j(i) P^(λ − c_i) E e_(x_i)   (BankPlacement::storage)
```

Its laws (Lean `HNN/IndexedOpen` §5, 9 theorems, standard axioms only):
- **normalization**: `Σ_k w_j(k) = 1` at `ρ > 0` (`framed_weight_mass`), and every datum weighs
  strictly more than zero (`framed_weight_pos`): no window;
- **one-sided on older data**: if every datum crosses at or before `j`, `w_j` is the one-way law
  read at any `e ≥ j`, the common factor `ρ^(e − τ_j)` cancelling (`framed_weight_one_sided`); so
  the open section (the request and the candidate) and any station read after every lock read
  exactly as before, and the diagnosis's clock-order replay is this law's reading;
- **a distant datum weighs little**: `w_j(k) = ρ^|τ_j − τ_k| w_j(j)` (`framed_weight_ratio`), and
  with the candidate in the span `w_j(k) ≤ ρ^|τ_j − τ_k|` (`framed_weight_le_pow`): station 7's lock
  read from station 0 at the frozen fit's `ρ` takes `[5/256, 3/128]` of the span, not
  `[205/256, 103/128]`;
- **two-sided and translation-free**: data at equal distance on either side weigh alike
  (`framed_weight_symmetric`), and a common shift of every tick and the station leaves every weight
  (`framed_weight_translation`);
- **lossless**: at `ρ = 1` every datum weighs `1/|span|` from every station
  (`framed_weight_lossless`); the card and the face path, which refuse a modulus below one, are
  unchanged;
- **the modulus's derivative**: `∂w_k/∂ρ = w_k (r_k − r̄)/ρ`, `r̄` the span's weighted mean distance
  from the station (the one-way law's form with each age replaced by the distance), held to the
  exact weights' central difference at second order by the owner's test; its Lean statement is owed
  (#62, §6).

**`ρ` stays the learned passive locus**: one at the founding, moved only by the certified committed
move (`hnn::executed`), held within `[ρ/2, 1]` on the source port's lattice.

**The modality statement.** The law reads only the distance between two ticks of the ring's clock,
never a datum's class or its meaning. A text cell at its tick, an image pixel at its scan tick, an
acoustic sample at its sample tick and a motor screw at its step are crossings of one clock. For an
image in scan order, a pixel's row neighbours sit one tick away on either side and weigh alike
(`framed_weight_symmetric`): a fill that locks the right neighbour first reads it exactly as it would
read the left one, which the one-way law could not; the pixels one row away sit at the row's width
`w` and weigh `ρ^w`, on either side. For audio the same holds for a sample's neighbours before and
after on the sample clock; for motion, for a screw's neighbours along the word. A second ring whose
clock advances by rows carries the transverse distance by the same law on that ring's clock (the
joint residue class); nothing modality-specific enters the law.

**Where the law is realized.** The bank reads every candidate from its own station
(`BankPlacement::storage(j, cells)`, `bank_release`), and so does the executed comparison, whose
pullback and certified move keep their form: the storage stays linear in `E` at fixed weights, so
each return is the placement's feature at the contribution's weight read from its station, and the
modulus's slope pairs each contribution's covector with its storage's derivative read from its
station (the owner's pullback test holds the identity exactly at `ρ = 1` and at `3/4`, where a
contribution's section holds a lock after its station). The readout path reads every station from
one anchor, whose weights are read at the span's last datum (`SourceMoment::phase_weights`): that
is each station's own law only for stations after every placed datum, so below modulus one the
readout refuses a passage with a placed datum after an open station (`Refinement::anchor_frames`);
its station-framed form is owed.

**What it does not repair** [agent-inferred]. A lock one tick away still weighs `ρ` times the
candidate, on either side. The diagnosis's clock-order losses (9 of 13 needing the lag-1
neighbour's amplitude, `E`'s key reading a lag-1 datum of the other chain as a lag-2 seed) are
this law's reading of past data, unchanged. `E`'s key must learn to discount that neighbour.

## 2. What is built (`fb871bb5`)

- `hnn::prediction::BankPlacement::{weights, storage, modulus_derivative}` (and the test's
  `exact_storage`) read from a station; `bank_release` reads each candidate from its own station;
  `Refinement::anchor_frames` and `HnnError::UnframedAnchor` refuse the readout's one anchor below
  modulus one where a placed datum follows an open station, in `stage`, `comparison_code` and
  `generate`.
- `hnn::executed`: each contribution carries its station; the returns, the modulus's slope, the
  storage moves, the first-order certificate, the face path's admission and the pairing receipt
  read from it.
- Lean `HNN/IndexedOpen` §5: `framedWeight` and 9 theorems.
- Tests: the placement framed at `ρ = 3/4` (the continued passage on past data exactly, the ratio
  `ρ^r` and the bound on either side, equal weights at equal distance, the one-way law's `ρ^(−3)`
  against the framed `ρ^3` from station 0, the derivative per frame, the anchor's refusal and
  `stage`'s); the pullback at `ρ = 1` and `3/4`.
- The probe (`model.placement_counts`, `eD_reentry.denominator_counts`) and the harnesses
  (`bank_causes -- {dump-read, native-release, reentry}`, `hnn_prediction -- executed {spread, move}`)
  read from the station.
- Atlas `hnn.station-framed-weights`; `hnn.passage-weights`, `hnn.bank-generation`,
  `hnn.release-comparison`, `hnn.executed-move` restated.

## 3. The acceptance, fixed before any measured run

1. **Every exact check holds**, every guard a commit guard: on every read release every lock
   certified, no refused certificate; every adopted move holds every guard (the harness prints each);
   the gates of the commit (`cargo check --workspace --all-targets`, `cargo test -p holonics --lib`,
   `bash tools/lean_check.sh Holonics HolonicsResearch`).
2. **The seed test** (the passage law pin's item 2, unchanged but for the law):
   - **2a, the acceptance.** The probe fits `E` and `ρ` on the release's own trajectory from the
     opening (`E₀` the sign sequence over two, `ρ = 1`) under the new law:
     `eO_fit.py order2 400 256 101 0.03 0.05 1 16`; the last `E` and `ρ` exported
     (`export.py … order2 1000104 128 … ρ`) and read natively from the open section
     (`bank_causes -- native-release`) on Stage 0's 128 held-out requests, `E` and `ρ` rounded to the
     source port's lattice. Reported: released, held, refused; **whole sections** against the
     passage law's 9 and the old law's 17 (of 128) and the diagnosis's open-section tops (9 of 16);
     **the first lock at station 0 or 1 and the first lock right** (against 0 and 128, and 44 and
     57); sections following the rule among their own stations; stations right by station; the two
     chains; native against float agreement; the fitted `ρ`. **Item 2 improves** when whole sections
     exceed 17 and the first lock is right more often than 57 (the passage law pin's criterion).
   - **2b, reported beside.** The frozen passage-law fit (its receipts' `seed_export.txt`) read
     natively under the new law on the same 128 requests: what the placement alone changes on the
     same constitution (its float column is the one-way law's release).
   - **2c, the re-entry diagnostic re-read** (`bank_causes -- reentry`) on the diagnosis's frozen
     export and its 16 development requests: the three storages (full, denominator alone, none) in
     clock order and in the release's own order, comparisons holding by insertion, where the first
     lost comparison now falls and whether the denominator alone still reproduces it; the ordinary and
     clock-order releases. The float prototype (`eD_reentry.py`) beside it.
   - **2d, reported beside.** The same diagnostic on 2a's fit (its export rebuilt on the 16
     development requests).
3. **Confirmation, only if item 2 improves** (the passage law pin's item 3, its seeds unread):
   `hnn_prediction -- executed train executed-open order2 2026093011 8 16 3600000 …` (the certified
   executed comparison trains `E` and `ρ` from the opening along the machine's own open-section
   trajectory, 16 moves of 8 fresh requests), then
   `executed evaluate order2 2026093012 128 … opening executed-open=…`. Reported: whole sections
   against the opening; the first request-dependent locks separately (the first lock at station 0 or
   1 and whether it is right); holds and incorrect releases; the trained `ρ`; the complete synthetic
   outputs. Passes when the trained constitution releases strictly more whole sections than the
   opening with item 1 holding. **Regressions**: the same arm, 8 moves of 8, on the alternation
   (training `2_026_093_013`, confirmation `2_026_093_014`) and the line (`2_026_093_015`,
   `2_026_093_016`), 128 requests each; each passes with no fewer whole sections than its opening.
4. **Time and memory**: every run within its deadline and a resident set of 4 GB; a run past its
   deadline is reported incomplete, never rerun with a larger one; no guard suspended.

## 4. The development read and the projections

The probe's fit under the new law at development seed 41, 16 steps (`eO_fit.py order2 16 256 41
0.03 0.05 1 16`, 9 held-out evaluations): 37 s, peak 142,020,608 bytes; `ρ` fell from 1 to between
`9/10` and `91/100`; releases began at step 4. The per-step cost equals the passage law's (its
400-step fit measured 1,042,057 ms): the new law changes only the weights' exponents. At `ρ = 1`
the new law is the old one, so the executed arm's first moves from the opening cost what the passage
law's development reads measured (5,721, 6,967 and 79,122 ms a move).

| Run | Projection | Deadline |
|---|---|---|
| 2a fit (float, 400 steps) | 1,000,000–1,600,000 ms | 2,400,000 ms |
| 2a and 2b native reads, 128 requests each | 400,000–600,000 ms each | 900,000 ms each |
| 2c and 2d re-entry diagnostics, 16 requests each | 100,000–300,000 ms each | 900,000 ms each (the harness's own guard) |
| order-2 training, 16 moves of 8 | 200,000–3,000,000 ms | 3,600,000 ms |
| order-2 confirmation, 2 × 128 | 100,000–700,000 ms | 1,200,000 ms |
| alternation and line training, 8 moves of 8 each | 100,000–1,800,000 ms each | 2,400,000 ms each |
| their confirmations, 2 × 128 each | 100,000–700,000 ms each | 1,200,000 ms each |

The runs go one at a time on the host's cores.

## 5. What is expected, named before the runs [agent-inferred]

- **2c**: in the release's own order the first losses at the first insertion fall (the far lock's
  mass is gone), and the denominator alone no longer reproduces most of them; the remaining losses
  sit where a lock one tick away is placed (the lag-1 amplitude), in both orders alike.
- **2b**: the frozen fit was fitted on far-end-first trajectories under the one-way law, where the
  first lock dominated every later reading; under the new law its later readings are near its
  open-section tops (972 of 1,024 right on these requests), less what a lag-1 lock costs. Whole
  sections above the passage law's 9 are expected; above 17 is not assured.
- **2a**: the refit trains on trajectories whose locks weigh `ρ^r` on either side, so `E`'s key can
  learn to discount a placed lag-1 datum of the other chain. **The expected blocker** is that
  secondary cause: if whole sections stay near the passage law's, the lag-1 neighbour's amplitude is
  the measured obstruction.

**Falsifiers:**
- the native owner and the float probe disagree on the new law's releases (the probe's mirror is
  wrong, not the law);
- in 2c the enlarged denominator alone still reproduces most first losses in the release's own order
  (the law did not remove the normalization's damage);
- the seed test does not improve (item 2's criterion);
- training improves and untouched confirmation does not;
- a resource bound is reached.

## 6. Owed in #62

"The station-framed placement" (September 30; `hnn::prediction::BankPlacement`; Lean
`HNN/IndexedOpen` §5 proves the framed weights' mass, positivity, one-sidedness on older data,
ratio, bound, symmetry, translation and the lossless case, and the one-way law's backward growth):
1. **The framed derivative**: `∂_ρ w_j(k) = w_j(k)(r_k − r̄)/ρ` as a `HasDerivAt` statement on
   `0 < ρ`, with the owner's `modulus_derivative` its instance (held by the test to second order).
2. **The stationary two-sided kernel**: that `ρ^|Δ|` is the stationary response of a first-order
   dissipative transport of modulus `ρ` a tick read in both directions (the tube's pairing reading),
   stated on the tube's owner (`Transport/ContinuingTube`).
3. **The phases' distances**: within one turn, a datum counted at phase `c` lies
   `1 + j + ((τ − c) mod d)` ticks before station `j` (held on instances by the owner's tests).
4. **The readout's station-framed form**: one anchor per frame, or a reading that carries the
   frame through the refinement; until then refused below modulus one.
