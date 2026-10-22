# The native contact step is certified by rereading the same comparison

Refs #73 #62. Follows [the retention decision](2026-10-22_RETENTION_RELEASES_ONLY_WHAT_NO_RECEIVER_CAN_READ_AND_THE_FACTOR_LOCI_TAKE_THE_LATTICE_RULE.md),
which located the contact's silence in the step size, and [the first-variation closeout](2026-10-22_REPRESENTED_NATIVE_CONTACT_FIRST_VARIATION.md),
whose connected control published zero factor motion with 96 released tails. Status:
[definition; agent-inferred, October 22], built and measured on the host.

## The cause

`CertifiedStep::certify(a, C, c)` takes the exponent `min(⌊log₂(a/C)⌋, ⌊log₂(1/c)⌋)`. On the
represented native route the curvature bound is `C = ½·response²`, about `2^43` on the connected
fixture, so every family's exponent landed in `−52..−37`. Against the contact factors' fine unit
`2^(−30)`, all 96 C/K/D updates fell below half a cell and were released. Retention was lawful
(the retention record); the step was too small to reach a unit.

`C` is an envelope over every ray at the held opening. The plan's §16 law says the step is
certified by rereading the same comparison, and the classic landing route already does that
(`first_reach`, `FiniteDecrease`, `decide`, `continuation.rs`). It refused charted operands, so the
native route never reached it.

## The decision

The native contact step is certified by a ladder that rereads the comparison it learned from.

1. Each family starts at its covector-scale bound alone (`ηc ≤ 1`, `StepSource::Reread`), then
   takes one common halving `h = 0, 1, …`.
2. The candidate `θ_h` is staged by `Constitution::deposited_with_contact_spans_reread`. The
   ladder stops with no publication when no factor entry moves, or when `h` passes the no-reach
   halving (`comparison::no_reach_halving_of`).
3. The existing first-variation witness (`native_contact_actual_ray`) runs first. A candidate it
   refuses is halved, never published.
4. A fork of the resident takes `θ_h` and prepares the same native prediction: the same opening,
   source, prepared input, receiver, target and bits. The objective is the classical loss read at
   the receiver's face, `code = Σ −log₂ p̂(t)`, beside the phase excess
   `X = Σ ½(φ_t − w_(2t+1)/2)²` (`native_objective`).
5. `decide(code, X, code′, X′, witness)` admits a strict improvement. An overlap or equal endpoint
   at the reading's bits is reread at 128 bits.
6. The first admitted halving is published (`publish_contact_carry_at`). If none is admitted, the
   certified step is published as before.

The receipt (`NativeRereadReceipt`) keeps the before reading, every trial, its first-variation
verdict and the decision.

What it repeats from the lessons, and why it is refused there: no authored routine stands in for
learning (the step is read from the machine's own comparison); no bits are read as progress
(admission is an exact strict decrease of the same comparison, phase part kept); seen material is
not graded as unseen (the reread is the contact's own comparison and is reported as such).

## The measurement

`represented_native_zero_motion_continuity` (`solenoidal_alpha`, host, debug build, source
`c8fd280bd`): pending-six cold restore, first R, contact at cell 10, next R, source 30 close, final
cold restore and four frozen decisions. Receipts:
[control.txt](2026-10-22_native_contact_reread_receipts/control.txt),
[counts.json](2026-10-22_native_contact_reread_receipts/counts.json).

- **The contact moves.** Outcome `Applied`, positive material influence, six steps selected. The
  family exponents are `2` on channel 0 and `−1` on channel 1, against `−52..−37` before.
- **The comparison improves exactly.** At halving 0, the same native prediction reads
  `39500519731543959171/2^64 ≈ 2.1413` bits before and `18344894552933922075/2^63 ≈ 1.9890` bits
  after (both endpoints equal at 64 bits), a decrease of about 0.152 bits. The phase excess is 0
  on both sides. The decision is `Classical`.
- **Continuity holds.** Cold restores after the contact and after source 30 are byte-equal with
  their pending state, both R sections pass, and the four frozen decisions pass.
- **Cost.** 506 native attempts (407 constructors, 39 companions, 30 actual and 30 fresh
  returns), 69.98 s wall. Projected 1–3 minutes before launch.

The improvement is on the comparison the step learned from, one cell. It is not a held-out reading.

## The stream learns its contacts at its section crossings

[definition; agent-inferred, October 22] The R-only delivery (`ObservedStream::receive_native_current`)
never published contact material. `ObservedStream::receive_native_current_learning` now publishes
one contact event wherever the source frontier stands at a section start with nothing pending,
that is, right after the receiver crosses its section. The next actual class is predicted under
the material the crossing just published, and its comparison deposits C/K/D by the ladder above.
The remaining classes of the section enter R as before. The schedule is the receiver's own
passage, as the Athena plan requires of contact grain, never a count of deposits. A contact the
native route refuses leaves the stream unchanged, its class enters R, and the refusal is returned.

**The first-variation enclosure is a reading under the reread.** The first held-out run refused
the second contact (source 20) at the represented first-variation enclosure: its error charges
exceeded the stored pairing, so its lower bound was not positive. That enclosure bounds a
derivative; the reread reads the finite step's consequence exactly, the same certificate the
finite-decrease landing uses. Under `StepSource::Reread` the enclosure is therefore read beside
each candidate (`NativeRereadTrial::first_variation_refused`) and gates nothing; the certified
fallback keeps its gate (`Constitution::native_contact_actual_ray_at`).

`represented_native_contact_learning_held_out` (same fixture and opening as above; cells 10–30
delivered two ways from the same state after the first R section):

| Arm | Contacts | Held-out code, cells 30–39 |
|---|---|---|
| R-only (`receive_native_current`) | none | 18.736 bits |
| Contact learning (`receive_native_current_learning`) | 2 published, 0 refused | 18.563 bits |

- At source 10 the contact lowers its own comparison from 2.141 to 1.989 bits; at source 20 from
  2.194 to 2.102 bits. Both are admitted at halving 0.
- The held-out read freezes each arm's retained state and predicts cells 30–39 one at a time,
  conditioned on the true earlier cells, with no learning (`native_current_query_fork`,
  `continue_native_current_forecast`). The contact arm's total is strictly lower:
  `342424543189510055705/2^64 < 345611777425719661287/2^64`. Five of the ten cells are lower.
- Flat over four classes is 20 bits; the data are periodic with period 4, so both arms are far
  from what the source allows. This is 30 training cells; it shows the contacts' learning reaches
  unseen cells, not that the learner is good.
- 80.8 s wall, host, debug build. Receipt:
  [held_out.txt](2026-10-22_native_contact_reread_receipts/held_out.txt).

## Athena's training commands never train contacts

The complete-language driver (`tools/complete_language.py`) runs `complete-language train`, which
is the observed-epoch route with scope `NormalMaps` (`examples/solenoidal_alpha/complete_language.rs`):
receiving maps only. No train command selects a scope with contact material. The observed-epoch
route's own material scope (`NormalMapsAndChannelMaterial`, reachable through the Alpha CLI's
`fork-scope`) sizes its steps by the a-priori certified step and admits only a non-increase; on a
64-cell excerpt it published no factor motion in any of its six epochs (one whole, three neutral,
two receiving-only after "the actual epoch ray violates its own curvature bound"). Athena's
training has so far learned its receiving maps alone. The native route with contact learning is
the route that now learns both.

## Athena's native training command

`complete-language train-native CORPUS SHA POPULATION OUT` and `complete-language sample-native
STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA CELLS OUT`
(`examples/solenoidal_alpha/complete_language/native_train.rs`, host only). Training opens the
native resident the controls use, turns the corpus into base-four cells and delivers it one
receiver section at a time through `receive_native_current_learning`, so each section's crossing
publishes one contact. After every section it prints the prequential code of the cells it scored
(each event's score of its actual class before learning it) and saves the whole state (native
continuing state, crib and pending cells). Sampling restores that state cold, conditions a frozen
fork on the prompt without learning, and releases one keyed cell at a time
(`release_native_current_forecast`), decoded by `Base4Bytes`.

First reading: the 16 bytes `The HNN is a Hol` (from THE_MACHINE), 64 cells, host, optimized build
without LTO, 4 cores. Receipts:
[train_native_16_bytes.txt](2026-10-22_native_contact_reread_receipts/train_native_16_bytes.txt)
(its first run), [train_native_16_bytes_split.txt](2026-10-22_native_contact_reread_receipts/train_native_16_bytes_split.txt)
(the same run with the contact time and Word opens per section),
[sample_native_16_cells.txt](2026-10-22_native_contact_reread_receipts/sample_native_16_cells.txt).

- 7 contacts published, none refused. Debug and optimized builds saved byte-identical states.
- Prequential code over the 61 scored cells: 2.021 bits per cell, against 2 for a flat guess.
  Sixteen bytes teach nothing measurable.
- Cost: 57.6 s, about 0.9 s per cell. Each steady section of 10 cells takes about 9.5 s: the
  contact (one cell and its ladder) about 4 s, the 9 receiving cells about 5.5 s; 123 Word opens
  per section. The saved state is about 2.6 MB of text, almost all of it the lagged receiver
  material M (four exact matrices of 17,646 entries each); it widens slowly with the cells but
  does not grow in count, and saving it costs about 0.9 s per section.
- Sampling 16 cells took 4.3 s (0.14 s per released cell, 1.6 s for the cold restore). The four
  released bytes are `B4 9E BA CF`, not text.

At about 4 s per byte, the native route cannot yet train on a real text. Its per-cell cost is the
next loop's subject.

### The first cost cuts

[definition; agent-inferred, October 22] A call-graph profile of 20 cells (optimized build) put
65% of each receiving cell in `NativePredictionWord::observe`'s contact pull-back
(`return_contact`), whose result the R section discarded: R publication reads only the receiving
face. Three cuts, each leaving the saved state byte-identical
(`eb028b8a558151c6331b4cb28027b87f6ab49df82eb9be8cfec7c66769c5e6b3`):

1. A receiving cell returns its face alone (`NativePredictionWord::observe_receiving`); the
   contact pull-back runs only at the contact. Return attempts on the 64 cells fell from 61 to 7.
   57.6 s became 41.5 s.
2. The ladder staged the admitted candidate, and read its first variation, once; the publication
   and its continuation staged it twice more and read the first variation twice more, once
   discarded. The ladder now hands its deposit, loaded spans, candidate, deposit reading and
   first-variation reading to the publication (`NativeRereadAdmission`). 31.2 s.
3. The state is saved where the aeon closes and after the last cell, not after every section.
   27.8 s.

Each steady section of 10 cells now takes about 4.6 s: the contact cell about 2.3 s, the nine
receiving cells about 2.2 s. That is about 1.9 s per byte, still far from a real text.

Both controls read the same values as before on the optimized build: every cold-restore size,
reread and verdict of the continuity control, and every held-out code of the learning control. The
continuity control's native attempts fall from 506 to 448 (actual and fresh returns 30 + 30 →
1 + 1). Receipts: [train_native_16_bytes_staged_once.txt](2026-10-22_native_contact_reread_receipts/train_native_16_bytes_staged_once.txt),
[train_native_16_bytes_aeon_save.txt](2026-10-22_native_contact_reread_receipts/train_native_16_bytes_aeon_save.txt),
[control_after_cost_cuts.txt](2026-10-22_native_contact_reread_receipts/control_after_cost_cuts.txt),
[held_out_after_cost_cuts.txt](2026-10-22_native_contact_reread_receipts/held_out_after_cost_cuts.txt).

### The arithmetic cuts

[definition; agent-inferred, October 22] The next profile put 60% of all instructions in the
greatest common divisor of `num-bigint` 0.4.8. Its binary gcd removes one bit per step, so reducing
an odd numerator against a denominator `2^k` walks the numerator's whole length, and every rational
product calls it three times. Three cuts, each leaving every saved state byte-identical:

4. `vendor/num-bigint` is that crate with one changed routine (`[patch.crates-io]` in the
   workspace manifest): the gcd splits off the common twos once, reduces by remainder while the
   operands differ in length by more than a bit and by subtraction otherwise, and finishes in one
   machine word. Its test compares it with Euclid's algorithm.
5. The context memory's moments `H += f fᴴ` and `B += η fᴴ` are formed over each vector's one
   shared denominator: Gaussian-integer numerator products, reduced once per entry. H is Hermitian,
   so each off-diagonal entry is formed once and its mirror is its conjugate.
6. The fit's residual `‖M H − B‖₁` sums `M_k H_kj` over the shared denominators of H and of the
   applied row, reduced once per entry, and the dyadic proposal divides by its power-of-two scale
   with a signed shift. The atlas row is `hnn.material-shared-denominator-moments`.

On the first 40 bytes of THE_MACHINE (160 cells) the run fell from 79.7 s to 58.1 s with the same
state (`db4b4f5597d616f47b432cdba6f28636375bf4caa9dc240f17d4acc57c4c8d78`); a steady section from
4.9 s to 3.4 s (the contact cell 2.5 to 1.9 s, the nine receiving cells 2.4 to 1.5 s). The 16-byte
state stays `eb028b8a…`. Both controls read the same values and the same native work counts; the
continuity control took 9.6 s instead of 15.5 s, the held-out control 10.3 s instead of 13.3 s.
Receipts: [train_native_160_cells_arithmetic_cuts.txt](2026-10-22_native_contact_reread_receipts/train_native_160_cells_arithmetic_cuts.txt),
[control_after_material_cuts.txt](2026-10-22_native_contact_reread_receipts/control_after_material_cuts.txt),
[held_out_after_material_cuts.txt](2026-10-22_native_contact_reread_receipts/held_out_after_material_cuts.txt).

### The first kilobyte, incomplete

The first 1024 bytes of THE_MACHINE (4096 cells), on the binary before the arithmetic cuts and
sharing the 4 cores with a profile, were projected at about 35 minutes with a 40-minute deadline.
After 830 s and 1030 cells the measured rate, 0.8 s per cell, showed the deadline would pass, and
the run was stopped. Receipt: [train_native_1k_partial.txt](2026-10-22_native_contact_reread_receipts/train_native_1k_partial.txt).

| Cells | 1–100 | 101–200 | 201–300 | 301–400 | 401–500 | 501–600 | 601–700 | 701–800 | 801–900 | 901–1000 |
|---|---|---|---|---|---|---|---|---|---|---|
| Code, bits per cell | 1.977 | 1.909 | 1.889 | 1.830 | 2.018 | 1.973 | 1.936 | 1.888 | 1.880 | 1.970 |

- Flat over four classes is 2 bits per cell. The code stays a little below it and does not fall
  steadily over the first thousand cells.
- 85 contacts were published and 18 refused, the first at cell 350. A section whose contact is
  refused took 17.7 s against 5.1 s for one that publishes: its ladder halves to the end without
  an admission. Refused sections took about 40% of the run.
- From the state saved at cell 1020, after the prompt `# The machine: ` (the corpus's own opening,
  which the prompt reread coded at 1.86 bits per cell), 80 released cells decode to the bytes
  `64 5f f5 cf ce 4e 22 69 84 b7 7f 3f 2e 1a 34 4f 25 11 14 b4`, not text. Six of the twenty have
  a first base-four digit above 1, which ASCII text never has. Receipt:
  [sample_native_1020_cells.txt](2026-10-22_native_contact_reread_receipts/sample_native_1020_cells.txt).

### A repeating sequence is learned slowly

64 bytes of `0x1B` give 256 cells whose base-four digits repeat `0,1,2,3` exactly, so a receiver
that holds the period can code every cell after the first period at 0 bits. With the arithmetic
cuts and the per-digit reading, the run took 89.7 s against a 90 s projection (deadline 300 s).
Receipt: [train_native_periodic_256_cells.txt](2026-10-22_native_contact_reread_receipts/train_native_periodic_256_cells.txt).

| Cells | 1–60 | 61–120 | 121–180 | 181–240 | 241–251 |
|---|---|---|---|---|---|
| Code, bits per cell | 1.898 | 1.661 | 1.584 | 1.539 | 1.647 |

- The code falls, so the contacts and the context material do learn, but after 25 contacts it is
  still 1.67 bits per cell over the whole run; by digit position `[1.542, 1.779, 1.674, 1.683]`.
- One contact was refused (cell 240), at 13.2 s for its section against about 3.1 s for the others.
- This is the measured blocker for text: the learning per contact is too small to hold even an
  exact period within a few hundred cells. It is the next loop's subject, before any longer text.

## What stays owed (#62)

- The Lean statement that the ladder's admitted step decreases the declared comparison
  (the composition of `decide`'s strict-decrease clause with the native objective).
- The phase excess reads 0 on this fixture, so the phase part of the comparison is untested here.
