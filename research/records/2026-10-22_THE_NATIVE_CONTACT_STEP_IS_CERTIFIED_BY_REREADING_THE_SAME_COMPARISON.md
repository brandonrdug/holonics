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

## What the measurement found

The native training stream never publishes contact material.
`ObservedStream::receive_native_current` (`observed/stream.rs`) delivers R sections only: the
receiving map learns, the contact factors do not. Contacts publish only through
`observe_native_current_contact`, which needs a closed, empty pending frontier, and only the
control calls it. The join owed next is the stream's own contact publication at its closed
section boundaries, so that ingestion moves C/K/D as well as R.

## What stays owed (#62)

- The Lean statement that the ladder's admitted step decreases the declared comparison
  (the composition of `decide`'s strict-decrease clause with the native objective).
- A downstream reading: whether the published motion lowers the code of later, unseen cells.
- The phase excess reads 0 on this fixture, so the phase part of the comparison is untested here.
