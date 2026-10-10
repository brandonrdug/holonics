# A bank of rings sounds its emission on a bounded lattice

October 10. Refs #386 (the helical code: the render is the decoder side of the strand the rings
carry), #148 (applications), #73. Continues
[the matched wave](2026-10-09_A_MATCHED_WAVE_ENTERS_A_LOADED_RING_AND_ITS_STATE_CROSSES_ITS_OWN_SECTION.md)
§9, which left owed "the render `g·Σ_b b_out = q + r`" and "the bounded (lattice) realization of the
carried state" (the exact state's denominators grow by the factor 145 per tick there).

## 1. The question, and the acceptance fixed first

Can the machine's own rings, driven by a real recording through their matched ports, be heard?
This is the first acoustic release: what the bank's carried state emits while the recording drives
it and after it stops. Brandon's perception is the measurement of what it sounds like. This record
fixes only what can be checked exactly.

**Acceptance (fixed before code):**

- **A1, the bounded carry.** On a declared lattice `2^(−L)`, every tick of every ring is
  `ResonatorOperands::step` with that lattice, an exact solve, and the state split by the
  error-feedback carry (`hnn::chart::carry`, Lean `feedback_tick`), with the remainders carried in
  the port from tick to tick. Every carried state entry lies on the lattice. Every tick's executed
  balance closes, `E′ − E = W_port − hωDω + chart + split`, with `|chart| ≤ chart_bound` and
  `|split| ≤ split_bound` (`ResonatorStep::closes`). Over the whole stream,
  `E_end − E_0 = Σ W_port − Σ hωDω + Σ (chart + split)` exactly.
- **A2, the render.** The emission of ring `b` at tick `n` is `e_b = b_b − a = −(2/Y_b) ω_b`, the
  part of the reflected wave the ring produces: the direct reflection `a` is the source's own. The
  rendered sample is one feedback tick at the 16-bit PCM lattice,
  `g·Σ_b e_b + r_(n−1) = q_n 2^(−15) + r_n` with `|r_n| ≤ 2^(−16)`. The gain `g` is the largest `2^(−k)`
  with `g · peak ≤ 1 − 2^(−14)`, the declared headroom ceiling, a normalization at the exterior
  boundary read from the emission's own peak; the ceiling guarantees every `|q_n| ≤ 2^15 − 1` after
  one feedback tick. It is maximal under that ceiling, not among every gain whose samples fit
  (corrected October 10 on Codex's review: a single amplitude `1 − 2^(−15)` fits at gain `1`, while
  the ceiling selects `1/2`).
- **A3, the stream is one.** Receiving the recording in chunks leaves the same states, remainders and
  render as receiving it whole.
- **A4, the output.** A 16-bit mono file at the recording's rate: the recording's length followed by
  one second of continuation (incident `a = 0`, the rings emitting what they hold).

**Not claimed:** that the bank is learned or located (it is declared, §2); that anything is
generated, predicted or recognized; any quality or fidelity reading. The boundedness is for the fixed
rational bank and the fixed PCM grain; the chunk equivalence (A3) is for a shared gain and the
continued state; the whole window's PCM remainder accounts for the summed quantization error, not
for any reconstruction of the source. The output is the bank's
response, a release of its dynamics, and is never compared with an invented control.

## 2. The declared bank, and each choice with its reason

[agent-inferred] The rings are the replica's declared ring (`tests/acoustic_wave_port.rs`
`declared_ring`): `C = I`, `D = 0`, `K = 4(a² + t²)`, `Y = 1/(4a)`, one complex node, `h = 1` tick
per sample. `t = tan(θ/2)` fixes the ring's turn per tick `θ`, and `a` its port coupling.

- **The turns.** `t_b = (1/50)(6/5)^b` for `b = 0, …, 23`: a geometric ladder of exact rationals with
  ratio `6/5`, chosen so that the ring's turn per tick is rational in `t` without any transcendental
  declaration. It spans `θ = 2 atan(t)` from about `2/50` rad per tick (near 100 Hz at 16000 Hz) to
  `2 atan(t_23)` (above 4 kHz). The frequencies are readings of `t`, not inputs.
- **The coupling.** `a_b = t_b / 32`: one quality for the whole ladder (the replica's bank used
  `a = t/8`). The ring then holds its state for about `32/t_b` ticks after the drive stops, so the
  continuation is audible.
- **The lattice.** `L = 32`, seventeen binary orders below the recording's grain `2^(−15)`.
- **The calibration.** A 16-bit sample `s` enters as the amplitude `a = s · 2^(−15)`, exact. That is
  the boundary chart, and it declares nothing of meaning.

## 3. Owners

| Law | Owner |
|---|---|
| the tick on a lattice, its balance and bounds | `hnn::ring::ResonatorOperands::step`, `ResonatorStep::closes` |
| the error-feedback carry | `hnn::chart::carry` (Lean `feedback_tick`) |
| the continuing port, now on a lattice | `hnn::wave::WavePort::on_lattice` (this record) |
| the boundary codec (16-bit PCM in and out) and the bank | `examples/acoustic_release.rs` (exterior only) |

## 4. Measured

[measured] One development read (2000 recorded and 500 continuation ticks) and one full run
([receipt](receipts/2026-10-10-acoustic-release/RELEASE_RUN.v1.json)). The full run covered the
recording's 93680 ticks (`= 2⁴·5·1171`) and 16000 continuation ticks, 24 rings on 12 threads, in
207570405132 ns against a projection of about 210 s (deadline 300 s), with a peak resident set of
209036 KiB.

- **A1 holds.**
  - Every tick of every ring closed (`ReceivedTick::closes`), and every carried state entry lay on
    `2^(−32)`.
  - Each ring's whole-stream balance `E_end = ΣW − ΣhωDω + Σ(chart + split)` closed exactly.
    `ΣhωDω = 0` because `D = 0`: the rings lose energy only through their ports.
  - The lattice's chart and split terms over the whole stream lie between `2⁻³³` and `2⁻²⁵` in
    magnitude per ring. They are booked, not hidden: on several rings the net port work is negative
    by exactly that amount, the rounding energy the ring returned through its port.
  - The carried state's widest entries stay within 75 bits.
  - The remainders' bits are those of the first 2500 ticks, within one bit (ring 22: 248 then 249).
    Every remainder stays below `2⁻³³`, so the carry is bounded in time.
  - On the exact law, the same port's state denominators grow with the ticks
    (`the_port_on_a_lattice_carries_a_bounded_state_and_every_tick_closes`).
- **A2 holds.** The emission's peak is in `[2⁻¹, 2⁰)`, so `g = 2⁰`. The render is one feedback tick
  per sample at `2⁻¹⁵`, and the final remainder is in `[2⁻³⁵, 2⁻³⁴)`. The peak sample is 19242 of 32767.
- **A3** is the test `the_lattice_port_carries_its_remainders_across_chunks`. The run itself received
  the stream in chunks of 8000.
- **A4.** The rendered file has 109680 samples. Its per-second sums of squares are, in order,
  `84300621938, 192651157656, 121257520412, 142463995040, 95539722630, 49067397092, 130`:
  - The last second, which is continuation only, has the sum 130 and the peak 1.
  - The bank's memory at `a = t/32` is about `32/t_b` ticks: 1600 ticks for the lowest ring and fewer
    for the higher ones.
  - The continuation is therefore audible for about the first tenth of a second after the recording
    ends and is silent after that.

The render went to Brandon whole, as it is. It is not committed, because it derives from the
private dataset directory.

## 5. What this rung is, and what the release still needs

The rung's claim is A1–A4: a bounded, exactly balanced port, and an exact render of what the rings
emit. It is not the requested release. That release needs:
- the machine's **located** keys: the rings' locks and section words, read from its own dynamics
  (`hnn::dynamic_section`, `hnn::section_lock`), not a declared bank;
- their **decoder**: sound produced from the located keys, with the exact residual of what they do
  not carry, `x = decode(keys) + e`, and both lengths paid (the reciprocal code of Codex's handoff).

No echo and no authored table stands in for it. The emission rendered here is the response of
declared rings to the recording, which is close to a filtered echo, and it is offered only as that.

The next rung's joins, at their actual consumers:
- the lock's winding as `geometry::winding::closed_loop_winding` over the class increments, which
  `section_lock` recomputes today by hand;
- the section word's concatenation law, `W(uv) = W(u) + W(v)` at a matching class, with the strand
  face `m(uv) = m(u) + x^|u| m(v)` (`HelicalCode.strandFace_append`);
- the decoder: the rings driven from their located locks, rendered by this rung's port and render,
  with the residual against the recording read exactly.

## 6. Recorded failures checked

- **An authored routine standing in for learning:** the bank is declared and says so. Nothing is
  claimed to be located or learned.
- **Recitation or echo counted as generation:** the emission is called a response (§5), never a
  generation.
- **Modality code outside the boundary:** the WAV codec lives only in the example. The port, the
  carry and the render are the ring's and the chart's owners.
- **A refusal answered with a larger limit:** the projection and deadline were fixed from the
  development read, and the run finished within them.
- **Bits read as progress:** no code length is claimed.

## 7. The second rung: each ring decodes its own moment keys (acceptance fixed before code)

[definition; agent-inferred, October 10] **The keys are the rings' moments at their own epochs.** A
linear ring driven by `x` carries `s_n = T^(n−m) s_m + Σ_(m≤j<n) T^(n−1−j) B x_j`. This is the chunking
law of `hnn::wave`'s header, and it is the helical code's strand face with the ring as the navigator:
the state is the phase-carried moment of everything that drove it. The ring's **epochs** are
intervals between its own section arrivals (`hnn::dynamic_section`: the whole winding `⌊ℓ/4⌋` of its
actual driven state). A **key** is the ring's state at the arrival that opens an epoch, at the key
grain `2^(−16)`, together with that arrival's tick (its placement). Nothing in a key is authored:
the arrivals are crossings of the ring's own state, and the state is its own moment.

- **The epoch's length is the ring's own half-memory.** `W_b` is the least number of whole turns
  after which the free ring (`a = 0` incident) holds at most half the energy it started with, read
  from the ring's own free run from a unit state on its lattice. A key opens at the first arrival,
  and then at each arrival whose whole winding is at least `W_b` past the last key's.
- **The decoder is the same ring, free between keys.** A second lattice port of the same operands
  receives incident `0` throughout. At each key's tick its state is seated to the key
  (`WavePort::seat`: the key as the action that sets the navigator's initial configuration, its work
  `E(key) − E(before)` booked). The decoded emission is that port's `ê_b = −(2/Y_b) ω̂_b`.
- **The residual is exact.** `R_n = Σ_b e_b(n) − Σ_b ê_b(n)` per tick, an exact rational. By the
  moment law it is the drive each epoch received after its key (and the key grain's remainder).

**Acceptance (fixed before code):**
- **B1.** The decoder's every tick closes, and its whole-stream balance closes exactly with the seat
  work booked: `E_end = ΣW − ΣhωDω + Σ(chart + split) + Σ seat`.
- **B2.** `Σ_b e_b = Σ_b ê_b + R` holds exactly at every tick.
- **B3.** Each ring's `W_b`, the key count, the arrivals the reader refused (a chord through the
  origin restarts the reader and is counted), and the keys' lengths are reported. The lengths are
  each key's two integers at `2^(−16)` and its tick gap under the Elias gamma code (`2⌊log₂ n⌋ + 1`
  bits for `n ≥ 1`, sign one bit), named as such and never read as progress.
- **B4.** The decode, rendered by the same render law, goes to Brandon whole. (Amended before the
  first run: each stream is rendered with its own boundary gain, which is reported. A seated key can
  raise the decoded peak above the emission's, and one shared gain could then overflow 16 bits.) The residual's per-second sums of squares at the PCM grain are reported beside the
  decode's, as exact integers.

**Not claimed:** compression, intelligibility or any quality reading, which are Brandon's perception
to judge; that the bank is located (it is still declared, §2); a generation. The decode is what the
rings' own moment keys carry of the recording, nothing more.

## 8. Measured: the moment keys carry part of the recording, at more than twice its cost

[measured] A development read (2500 ticks, 9704554536 ns) and one full run
([receipt](receipts/2026-10-10-acoustic-release/DECODE_RUN.v1.json)): 405567075951 ns against a
projection of 425 s (deadline 480 s), with a peak resident set of 406952 KiB.

- **The encoder is unchanged.** The emission's render is byte-identical to §4's.
- **B1 holds.** Every decoder tick of every ring closed, and every decoder's whole-stream balance
  closed exactly with its seat work booked.
- **B2** holds by construction: `R` is defined as `Σe − Σê` in exact arithmetic. It adds no evidence
  beyond B1.
- **B3.**
  - The half-memory is 1 turn for rings 0–15, 2 turns for rings 16–21 and 3 turns for rings 22–23. At
    `a = t/32`, the free ring gives up about half its energy through its port in one turn.
  - There are 86446 keys in all, from 711 (ring 0) to 6841 (ring 21).
  - The reader restarted once on each of rings 0–5 and 9: their state passed through the origin in
    silence.
  - The keys' length under the Elias gamma code is 3872041 bits. The recording's own 16-bit samples
    are `93680 · 16 = 1498880` bits, and `2 · 1498880 < 3872041 < 3 · 1498880`.
- **B4.** The decode's peak is in `[2⁻², 2⁻¹)` (gain `2¹`), and the residual's in `[2⁻¹, 2⁰)` (gain
  `2⁰`). Per second, at those gains, the sums of squares are:

| second | emission (gain 2⁰) | decode (gain 2¹) | residual (gain 2⁰) |
|---|---|---|---|
| 0 | 84300621938 | 116590945411 | 61504029725 |
| 1 | 192651157656 | 324018482445 | 133939683102 |
| 2 | 121257520412 | 182533990404 | 72837255666 |
| 3 | 142463995040 | 201902092508 | 82487184684 |
| 4 | 95539722630 | 143235553289 | 57958910921 |
| 5 | 49067397092 | 76886180977 | 23992535841 |
| 6 | 130 | 265 | 14 |

  The decode's gain `2¹` multiplies its sums of squares by 4. At the emission's gain the decode would
  read about a quarter of each entry in its column, below the residual's entry in every second
  with recording in it. The decode went to Brandon whole.

**What the reading says.** On this declared bank, a ring forgets half of what it holds within one
turn. A key therefore carries little beyond its own epoch, and most of each epoch's emission is that
epoch's own drive: the residual, the news the key does not hold. The keys cost more than the samples
they replace. This is the measurement, and it names the blocker: **the declared bank's memory is
about one turn, so its moments are not a code of the recording**, whatever the recording sounds like
through them. Brandon's perception of the decode is the reading this record cannot make.

The next rung changes what is measured to have failed, not the limit. The rings must be located
from the recording, and their memory must be that of rings whose port coupling matches what they
hold (`hnn::section_lock`'s settled locks are the existing owner of a ring that has locked). Then a
key holds a lock across many turns, and only the lock's departures enter the residual.

## 9. The next rung: decode the source, not the emission (design; acceptance to be fixed before code)

[definition; agent-inferred, October 10, on Codex's join
`source[n] = decode(located_keys, constitution, frame, clock)[n] + residual[n]`] §7 decodes each ring's
*emission*. The release must decode the *source*. The moment law fixes how.

- **A key is a linear reading of the source.** `key_(b,k) = s_b(n_k) = Σ_(j<n_k) T_b^(n_k−1−j) B_b x_j`.
  Every key of every ring is one exact linear functional of the one recording `x`: the receivers'
  readings of the same source through their own navigators.
- **The decode is a point of the preimage fibre.** The sources consistent with all keys form an
  affine fibre `x̂ + ker K`, where `K` is the key map. The decode is the fibre's least-power point
  under the port's pairing (`(hY/4)|x|²`). It is the minimum-energy source that every ring would read
  as its keys. The residual `x − x̂` lies exactly in `ker K`: the differences no key distinguishes.
  That is the kernel the elementary objects name for compression, read here, not declared.
- **Locality.** A ring forgets (§8: half its energy per turn), so each key reads only the source
  within a few of its memories. `K` is banded in time, and the fibre's least point is solved epoch by
  epoch over overlapping windows. Exact rational elimination over the full recording is not
  admitted, because its numbers grow; the window and its carried boundary are the design's remaining
  decision, to be derived from the rings' memories before code.
- **Located rings.** §8's blocker stands: with a memory of one turn, the keys cost more than the
  samples. The bank's rings must hold what they read. Their turns and couplings are located from the
  recording by the existing lock owners (`hnn::section_lock`: a settled ring's lock `W/τ`), not
  declared, so that one key spans many turns of a locked ring.

The section words' omissions (amplitude, within-quadrant phase, placement detail) are the fibre's
directions. They stay in the decoder's retained constraints or in the residual, with their costs
accounted (Codex's review of the first rung).

## 10. Do the rings lock on this recording? (the lock census; reading fixed before the run)

[definition; agent-inferred, October 10] §9's located rings need locks that hold across many turns.
The existing lock owner (`hnn::section_lock::{LockReader, Settled::lock}`) is the reading. Each ring's
driven state is read in consecutive windows of four of its own turns, so that a period of up to two
turns shows twice. The ring's turn is the free run's first whole turn, from §7's half-memory read.
Each window is tallied as locked (with its winding over period), unlocked, silent or at rest, or
refused. The lock requires the window's symbols to repeat exactly, with no tolerance. The near-return
grain for a stretch that is only near-periodic is not built (matched-wave record §9).

**What decides the next rung.** If the speech's rings lock in a substantial share of windows, located
locks can carry keys across turns and §9 proceeds on the exact lock. If they rarely lock, the owed
near-return grain is §9's prerequisite, and its acceptance comes first.

[measured] **The census** ([receipt](receipts/2026-10-10-acoustic-release/LOCK_CENSUS.v1.json)):
192734411239 ns against a projection of about 210 s (deadline 300 s), with a peak resident set of
201684 KiB. Over all 24 rings, there were 52349 windows:

| reading | windows |
|---|---|
| locked | 6730 |
| unlocked | 45342 |
| silent or at rest | 270 |
| refused (a chord through the origin) | 7 |

- **The rings below about 400 Hz (0–6) almost never lock.** Rings 0–6 hold the voice's fundamental,
  read in windows of 212 to 632 ticks. Ring 0 locked in 5 of 173 windows, and rings 4–6 in 1 window
  each.
- **The middle and upper rings lock in about one window in nine to one in six** (ring 7: 77 of 619;
  ring 15: 352 of 2437; ring 22: 1087 of 6451). Ring 20 locked in 48 of 5222.
- **Nearly every lock is at the ring's own free turn or next to it.** Ring 11 locks at `1/20` against
  its free turn of 22 ticks, ring 15 at `1/10` against 11, and ring 21 at `1/4` against 5. A ring
  locks when one sinusoid dominates its band long enough for its symbols to repeat exactly. These are
  readings of the ring's resonance, not periodicities located in the speech: no lock in the
  fundamental's region holds across a voiced stretch.

**Decision, by the rule fixed before the run.** Exact locks do not carry this speech. The owed
near-return grain (matched-wave record §9: a lock for a stretch that is only near-periodic, its
departure kept in the fibre) is the prerequisite of §9's located rings. Its acceptance is the next
rung's first item.

## 11. The near-return grain (acceptance fixed before code)

[definition; agent-inferred, October 10] The exact lock (§10) admits a period only when the window's
symbols repeat with no exception. A near-periodic stretch repeats with exceptions. The grain must
not be a tolerance, which would be a declared literal. It is read as compression, with both lengths
paid:

```text
word      s_0 … s_(L−1)                                   the window's section symbols (hnn::dynamic_section)
cycle_τ   s_0 … s_(τ−1)                                   the first τ symbols
defects_τ {(k, Δℓ_k) : Δℓ_k ≠ Δℓ_(k mod τ)}              every tick whose advance the cycle does not predict, kept with it
L_raw     = L · ℓ_s                                       the word spelled symbol by symbol
L_τ       = γ(τ) + τ · ℓ_s + γ(|defects_τ| + 1) + Σ_defects (γ(gap) + ℓ_s)
near-return:  the least τ ≤ L/2 minimizing L_τ, admitted iff L_τ < L_raw;  else Unlocked
```

Here `ℓ_s` is the bits of one symbol under the section word's own law. The class follows from the
class recursion `class_(k+1) = class_k + Δℓ_k (mod 4)` and the crossing from `(class, Δℓ)`, so a
symbol carries only its advance `Δℓ ∈ {−2, …, 2}`: `ℓ_s = ⌈log₂ 5⌉ = 3`. The opening class costs
`2` bits in both `L_raw` and `L_τ`, so it cancels. A defect substitutes an advance. `γ` is the Elias
gamma length.

- **Nothing is lost.** The word is exactly the cycle repeated with the defects substituted, and
  `decode(cycle_τ, defects_τ) = word` is asserted. The defects are the lock's fibre (the section
  words' omitted detail, Codex's review), carried with their cost, not discarded.
- **The exact lock is the case with no defects.** A window that locks exactly at `τ₀` has a
  zero-defect description at `τ₀`, so it is admitted, at a length no greater than that.
- **The winding is the cycle's.** `W = Σ_(k<τ) Δℓ_k / 4` is admitted only when it is whole. The
  defects' own lift is read separately, `Σ_defects (Δℓ_k − Δℓ_(k mod τ))`, and is never folded into
  `W`.

**Acceptance.**
- **N1.** `decode = word` on every window read.
- **N2.** Every window the census locked is admitted, and its `L_τ` is at most the exact lock's
  zero-defect length `γ(τ₀) + 3τ₀ + 1`. A window whose minimizing `τ` differs from `τ₀` (a shorter
  cycle with a few defects that costs less) is counted and reported. (Amended before any code: under a
  description-length law the minimizing period need not be the least exact period.)
- **N3.** The census is repeated with the near-return grain, reporting per ring the windows admitted
  and the sum of `L_τ` against the sum of `L_raw`, as exact integers.
- **N4.** The owner is `hnn::section_lock`, beside the exact lock, after the winding join (in flight
  separately) lands, so that the two changes do not collide.

[measured] **N1 and N2 on the declared bank** ([receipt](receipts/2026-10-10-acoustic-release/NEAR_RETURN_TESTS.v1.json);
`acoustic_wave_port` 22 of 22 at the merged worktree).
- Under F1, F3 and F4, on every ring of the replica's bank, the near-return decodes its window's word
  exactly.
- Every exact lock is admitted, at a description no longer than its zero-defect one. Where it keeps
  `τ₀`, it has no defect and the same winding and address.
- The F1 wave with one sample raised by 7 after the settle allowance no longer locks exactly on the
  ring `t = 1`. Its near-return keeps the clean cycle, `τ = 7`, with 6 defects whose own lift is 8,
  read apart from the cycle's winding, and it describes the 120-tick window in 73 bits against 360.
- The census on the recording (N3) and the gate are pending.

[measured] **N3, the near-return census** ([receipt](receipts/2026-10-10-acoustic-release/NEAR_RETURN_CENSUS.v1.json)):
196162216019 ns against a projection of about 210 s (deadline 300 s). N1 was asserted on every window
read and held. Gate 1 passed at `68aece1a`.

| reading over all 24 rings | value |
|---|---|
| windows admitted as near-returns | 33395 (exact locks: 6730) |
| windows not admitted | 18733 |
| bits of the admitted descriptions | 2762870 |
| bits of the same windows spelled out | 6309636 |
| defects kept | 260254 |

- **The voice's rings are admitted, trivially** (corrected below, §13's period reading). Ring 0 admits
  172 of its 173 windows (exact locks: 5), described in 43991 bits against 326112, with 3284 defects
  kept. Every one of ring 0's non-turning admissions has period 1: the cycle is "advance 0", and the
  defects are the ray crossings. The bits measure that a slowly turning ring's word is mostly zeros,
  not a structure of the speech. Rings 1–5 admit 203, 233, 279, 328 and 384
  windows, each at between `1/7` and `3/10` of its raw length (the exact bits are in the receipt).
- **The upper rings admit fewer.** Ring 23 admits 2433 of 6451 windows. Its windows of 16 ticks
  leave little room for a cycle to pay for itself.
- **What this is.** It describes the section words, the rings' advances, and nothing else. A
  section word omits amplitude, within-quadrant phase and placement. Those stay in the fibre or the
  residual with their own costs, and a lossless section-word code does not by itself rebuild the
  waveform (Codex's review). The census shows that the rings' own clocks near-return through most of
  this speech, so located near-returns can carry keys across turns. It does not show a decoder.

## 12. The second rung's key clock, repaired (Codex's review of `fe4b6b63`)

The decoder's seating and balance kept source GO. Five defects were found in its key clock and its
statements. Each is closed below at the source after `68aece1a`. The original run (§8,
[receipt](receipts/2026-10-10-acoustic-release/DECODE_RUN.v1.json)) is kept as measured with the
defective clock.

1. **The half-memory was read inside a turn.** `half_memory` tested the energy at every tick once a
   whole turn had passed, so it returned the floor of the winding at the first halving tick. Exact
   witness on ring 0: the first whole return is at tick 158 (lift 4) with energy above `1/4`; the first
   halving tick is 290 (lift 7) with energy below `1/4`. The helper returned `W = 1` and discarded class
   3. **Closed:** the energy is now read only at the ring's complete section returns (positive
   arrivals), so `W` is the least whole-return count at which the free ring holds at most half its
   energy.
2. **A reader restart kept the last key's lift.** After a restart (the state through the origin, §8)
   the new reader's lift starts from its class, while `last_key` still named the old passage's whole
   winding, and the two were subtracted. **Closed:** a restart, and the reader's first start, clear
   `last_key`, so the next arrival opens a key and a new span. No winding is subtracted across
   passages.
3. **The key's dimension was misstated.** B3 said each key is two integers. The key is the ring's
   state `[u, w]` of one complex node: **four** integers at `2^(−16)`, the driven coordinate's two and
   the quadrature's two. §8's 3872041 gamma bits priced all four. The quadrature stays at rest for
   this isotropic node, and Codex computes 3699149 bits without its zeros' cost. **Closed:** the run
   now reports both, the four integers' cost and the quadrature's share. A packing that drops the
   zeros is not compression and is not presented as one.
4. **Two residuals, kept apart.** The decoder of §7 targets the bank's emission,
   `bank(source)[n] = decoded_keys[n] + R_bank[n]`. That is not the requested source reconstruction,
   `source[n] = decode(located_keys, constitution, frame, clock)[n] + R_source[n]` (§9). Each residual
   is read at its own consumer with its own cost. The keys do not carry the forcing that arrives
   during an epoch's free evolution. On the lattice, the moment law keeps its rounding terms,
   `s_n = T^(n−m) s_m + Σ_(m≤j<n) T^(n−1−j) (B x_j + ρ_j)`, where `ρ_j` is the error-feedback split of
   tick `j` (`hnn::chart::carry`); §7's statement omitted `ρ`.
5. **The residual-over-decode reading holds for the recording only.** §8 compares within the six
   seconds that hold the recording. In the continuation (second 6) the decode reads 265 at gain `2¹`,
   about 66 at the emission's gain, above the residual's 14.

The repaired decoder is to be rerun under the announced lane, and its measurement goes beside §8,
never over it.

[measured] **The repaired decoder** ([receipt](receipts/2026-10-10-acoustic-release/DECODE_REPAIRED_RUN.v1.json);
§8's run is kept beside it): 400859590067 ns against a projection of about 425 s (deadline 480 s), with
a peak resident set of 421544 KiB. Gate 1 passed at `293b19c4`. B1 held: every decoder tick and every
whole-stream balance with seats closed. The emission's render is unchanged.

- **The half-memory, read at complete returns:** 2 turns for rings 0–17 and 19, 3 for rings 18 and
  20–22, 4 for ring 23. §8's defective clock read 1 turn for rings 0–15.
- **The keys:** 56039 in all, against §8's 86446. Ring 0 has 356 keys (§8: 711).
- **The keys' length under the gamma code, four integers per key:** 2455192 bits. The quadrature's
  zeros are 112076 of those bits, which leaves 2343116. One key per ring can fall on the stream's
  last tick, where it opens no epoch and is not seated; the quadrature's count shows one such key in
  all. Against the recording's 1498880 bits: `1498880 < 2343116 < 2455192 < 2 · 1498880`. The keys
  still cost more than the samples they stand for, now by less than twice.
- **The renders, all at gain `2⁰`** (per second, sums of squares):

| second | emission | decode | residual `R_bank` |
|---|---|---|---|
| 0 | 84300621938 | 29858688978 | 63138906044 |
| 1 | 192651157656 | 94190053906 | 144603167496 |
| 2 | 121257520412 | 50072620369 | 82477282185 |
| 3 | 142463995040 | 54767801302 | 93445197990 |
| 4 | 95539722630 | 38789479270 | 71565583994 |
| 5 | 49067397092 | 19420221985 | 27306618823 |
| 6 | 130 | 128 | 0 |

  In every second that holds the recording, the residual exceeds the decode. In the continuation
  (second 6) the residual renders to exactly 0: with no drive, the decoder seated at its last key and
  the encoder ring evolve identically, to within the key grain, below the PCM grain.

**The blocker, restated with the repaired clock.** The declared bank's moments still cost more than
the samples, and they carry less of each epoch's emission than its own drive does. §9's located rings
and §11's near-returns, which describe the rings' section words in under half their length, remain
the way forward. The residual named here is the bank's, `R_bank`, not the source's.

## 13. The located rung (design; acceptance fixed before code)

[definition; agent-inferred, October 10] §8 and §12 measure why the declared bank's moments are not a
code: each ring forgets about half its energy per turn, so each key carries little beyond its own
epoch. §11 shows the rings' own clocks near-return through most of the speech. The located rung
therefore takes its rings from those returns, not from a declaration.

- **Locate.** In each near-return window of the declared bank, the cycle's address `W/τ` is a turn
  rate the speech held for at least two cycles. These readings are the located rates. Nothing names
  a pitch or a harmonic: the address is the ring's own reading of what drove it.
- **Located ring.** For a located rate `W/τ`, the ring is the declared ring's form
  (`C = I, D = 0, K = 4(a² + t²), Y = 1/(4a)`). Its `t` is the simplest rational in the Farey order
  whose free ring's own section word near-returns at exactly `W/τ`, read by running it. The coupling
  `a` is the largest dyadic whose free ring holds at least half its energy across the window's span,
  which is the memory the located return requires. Both are located by the ring's own dynamics; no
  table maps a rate to a frequency.
- **Keys and decoder.** As in §7, with §12's clock: keys at the located ring's own complete returns,
  one per half-memory, and the decoder seated at each key. The decoded source is §9's least-power
  fibre point of the keys of all located rings, solved per window, and `R_source = x − x̂` is exact.
- **Both lengths paid.** `L_keys` covers the located rates (each `W/τ` and its window's placement), the
  located rings' `t` and `a`, and the keys. `L_residual` covers `R_source` at the PCM grain. Both are
  under the stated integer codes. The raw length is `16` bits per sample.

**Acceptance (fixed before code).**
- **L1.** Every located ring's free section word near-returns at its located `W/τ`, read by
  `Settled::near_return`.
- **L2.** Every decoder balance closes with its seats (as B1).
- **L3.** `source = x̂ + R_source` exactly at every tick.
- **L4.** `L_keys`, `L_residual` and `16 · 93680` are reported. A code is claimed only if
  `L_keys + L_residual < 16 · 93680`. Otherwise the measurement names which term exceeds it.
- **L5.** The decode `x̂` goes to Brandon whole, rendered by the render law.

**Recorded failures checked.**
- **An authored routine standing in for learning:** the rates and rings are located by the machine's
  own returns and runs, and nothing is tuned to speech.
- **Bits read as progress:** L4 reports both lengths and claims only a strict inequality, with the
  decoder paid.
- **Echo counted as generation:** the decode is called a decode of keys, never a generation.

## 14. Obligations owed to #62

1. **The port on a lattice** (`WavePort::on_lattice`): a passive ring's tick with an exact solve and
   error-feedback splits of rate and state closes
   `E′ − E = (hY/4)(|a|² − |b|²) − hωDω + chart + split`, with `|chart| ≤ chart_bound` and
   `|split| ≤ split_bound`, and every carried state entry lies on the lattice (`HNN/Ring`'s
   `ring_tick_executed_energy_balance` and `feedback_tick` are the parts it composes).
2. **The seated key** (`WavePort::seat`): the whole-stream balance with seats,
   `E_end = ΣW − ΣhωDω + Σ(chart + split) + Σ(E(key) − E(before))`.
3. **The near-return** (`Settled::near_return`): `decode(cycle_τ, defects_τ) = word` for every
   admitted window. A word with least exact period `τ₀` and whole winding is admitted at a length of
   at most `γ(τ₀) + 3τ₀ + 1`. The cycle's winding is `closed_loop_winding` of its advances, and the
   defects' lift is `Σ_D (Δℓ_k − Δℓ_(k mod τ))`.
4. **The lattice moment law** (§12): `s_n = T^(n−m) s_m + Σ_(m≤j<n) T^(n−1−j) (B x_j + ρ_j)` for the
   port on a lattice, with `ρ_j` the tick's split.

[measured] **The locate step, read** ([receipt](receipts/2026-10-10-acoustic-release/LOCATED_RATES.v1.json)):
210204364415 ns against a projection of about 200 s (deadline 300 s). Gate 1 passed. Per ring, the
windows whose near-return turns (`W ≠ 0`) and their most read rates:

- **The voice's rings (0–5) almost never turn.** Ring 0 admitted 172 near-returns (§11), and only 2
  of them turn (`1/105`, `1/118`). Rings 1–5 turn in 10, 12, 9, 15 and 20 windows, each at a
  different rate. Their near-returns are non-turning cycles (`W = 0`): the state rocks across rays
  and returns without completing a turn.
- **The other rings turn at their own free rate.** Ring 7 turns in 117 windows, 70 of them at `1/40`
  (free turn 44 ticks). Ring 11 turns in 305, 171 at `1/20` (free turn 22). Ring 21 turns in 1581,
  1376 at `1/4` (free turn 5). The most read rate is the ring's resonance or its neighbour.

**The blocker, by its measurement.** §13's locate step, which takes rates from the turning
near-returns, would locate the declared bank's own resonances, not a structure of the recording.
Where the voice's fundamental lives, there are almost no turning returns to locate. The measured
object there is the non-turning near-return, whose cycle carries no winding, and the next design
reads it: what it holds (its cycle's advances and defects) and whether its period, not a winding,
is the located clock. L1 to L5 are not attempted on a located bank built from resonances. Building
it would repeat the recorded failure of an authored stand-in: a bank chosen to look located.

## 15. The architecture choice: the source through the ring's inverse tick, keyed on its own section word

[definition; agent-inferred, October 10; the decision for the 23:30 observation] No further ring-bank
variant. §8–§13 measure why: declared or resonance-located rings forget, and their moments cost more
than the samples. The source obligation, `source = decode(located_keys, constitution, frame, clock) +
R_source`, does not need a bank. It needs one ring's retained quotient, its exact inverse, and keys
located on the ring's own symbols by the existing key and repair owners.

- **The retained quotient.** One ring's carried state, its phase-carried moment on the lattice:
  `s_(n+1) = T s_n + B x_n + ρ_n`. It suffices for the ring's future (the retention law), and it
  determines the source exactly through the **inverse tick**,
  `x_n = B⁺ (s_(n+1) − T s_n − ρ_n)`, where `B` drives one real coordinate and `B⁺` is its exact left
  inverse there.
- **What the decoder consumes.** The state trajectory factors exactly as cell × fibre. The cell is
  the section symbol `(class, Δℓ)` at the quarter-turn grain with its carry (`hnn::dynamic_section`,
  which emerge from the ring's dynamics, with no authored alphabet). The fibre is the position inside
  the cell (the `GrainCell`'s unresolved fibre).
  - The section word is regenerated exactly from a key located on it: the near-return's cycle as the
    pair relation at offset `τ` (`compression::keys::repair::PairRelation`), its defects as the
    residual (`residual_code`), and `reopen` returning the word (`43788fb9`; Lean
    `Transport/Fold.reopen_apply_fold`).
  - The fibre is coded at a declared grain.
- **How the forcing reaches the decoder.** Free checkpoint evolution (§7, §12) loses the forcing that
  arrives inside an epoch. Here it arrives twice: where it changes the cell sequence it is the
  word's defects, already in the residual code; inside a cell it is the fibre. With the fibre at the
  lattice grain, `ŝ = s` and `x̂ = x` exactly. With a coarser fibre,
  `R_source[n] = B⁺(Δ_T (s − ŝ))[n]` exactly, where `Δ_T s = s_(n+1) − T s_n − ρ_n`. `R_bank` is not
  used.
- **Both lengths, together.** The shared decoder (the ring's `T`, `B`, `Y`, the lattice and the
  section chart), the key's code, the defects' code, the fibre's code at its grain, and `R_source`
  at the PCM grain, summed against `16 · N`.

**The concrete missing interfaces.**
- `hnn::section_lock::NearReturn → compression::keys::repair::{PairRelation, DamagedPassage}`: the
  section word as the repair owners' passage (its classes the advances `{−2, …, 2}`), so that
  `key_code`, `residual_code` and `reopen` give the paid exact codes in place of §11's own gamma count.
- The inverse tick at the port, `x_n = B⁺(s_(n+1) − T s_n − ρ_n)` on `hnn::wave::WavePort` (source
  read back from the carried state), with the consumer test `inverse_tick(port's states) = samples`
  exactly on the lattice port.

**The receiver equation, for review.**
`x_n = B⁺(ŝ_(n+1) − T ŝ_n − ρ̂_n) + R_source[n]`, with
`ŝ = cell(reopen(key_code, residual_code)) ⊕ fibre(grain)`.

**The next measurement.** The grain at which the fibre's code plus `R_source` falls below the
samples' own length, or a measurement that it does not, and where.

**Existing owners.**
- `compression::keys::{frames (1c6da214), transport, repair (43788fb9), duplex}`.
- `hnn::keys` and `hnn::moment` (`68fb967d`; `SourceMoment`, the field's own phase-carried moment,
  whose bridge to the strand face is owed in #62).
- `hnn::dynamic_section` (`b043cb8e`) and `hnn::section_lock` (`c55faacf`, the near-return above).

[measured] **The non-turning near-returns' periods** ([receipt](receipts/2026-10-10-acoustic-release/NEAR_RETURN_PERIODS.v1.json)):
203487886494 ns against a projection of about 210 s (deadline 300 s).

- **The voice's rings.** In rings 0–5 nearly every non-turning near-return has **period 1**: ring 0
  170 of 170, ring 1 192 of 193, ring 4 313 of 313. The "cycle" is the advance `0` repeated, and
  every ray crossing is a defect. A ring turning a quarter in tens of ticks reads mostly `0`, and its
  near-return says only that.
- **The upper rings.** Period 1 still leads, and the short periods near each ring's own turn follow
  (ring 19: 6, 11 and 5 ticks; ring 23: 7 and 3 ticks).
- **What it settles.** The hypothesis that the non-turning cycles hold the recording's clock is
  refuted on this bank. Their periods are trivial in the voice's rings and resonant above.
  - §11's N3 bits for the low rings are corrected accordingly: they measure sparse crossings, not a
    located return.
  - The information of a slow ring's word is in **where its crossings fall** (the defects'
    placement) and in the fibre. That is where §15's architecture puts it, through the repair
    owners' residual code and the fibre's code, read against the source by the inverse tick.

[measured] **Interface (b), the inverse tick, is built** (`ResonatorOperands::inverse_step`;
[receipt](receipts/2026-10-10-acoustic-release/INVERSE_TICK_TESTS.v1.json)). Every tick of the
declared ring `t = 1` under F1, on the exact law and on the lattice `2^(−32)`, read backwards from its
states and remainders, returns exactly its incident amplitude on the driven coordinate and zero on
the quadrature. A pair of states two ticks apart is refused. `acoustic_wave_port` passes 23 of 23,
and gate 1 is ok. The source is exactly one ring's inverse tick once its state and remainders are
known. The remaining question is §15's next measurement, at what grain they can be known.

## 16. The source through one ring's cells (§15's measurement; reading fixed before the result)

[definition; agent-inferred, October 10] With the inverse tick exact (§15), the source is coded
losslessly through one ring's dynamic symbols, and nothing outside the ring's own law enters.

- Given the ring's exact carried state `s_n`, the drive's image is affine in the sample,
  `ω = ω₀ + x m`. The two exact-law steps that read `ω₀` and `m` are the ring owner's own `step`.
- So the next state's cell, its quadrant at the section, bounds the sample to an interval of PCM
  values. The interval is widened by one value at each end for the lattice's rounding.
- The code per tick is the section word's symbol, at `3` bits, plus the sample's index in its
  interval, at `⌈log₂ count⌉` bits.
- The decoder holds the same state, reads the cell, computes the same interval, reads the index,
  recovers `x_n` exactly and steps. `R_source = 0`, and the residual is the index code itself.
- It was run on rings 0, 4, …, 20 over the recording's 93680 ticks.

**Reading rule (fixed at launch).** A ring's dynamic symbols carry the source more cheaply than the
samples only if `word bits + index bits < 16 · 93680 = 1498880`. Otherwise the measurement names how
much the cells narrow each sample (the index bits) against what the cells cost (the word bits).
Under ideal codes the chain rule makes the two factorizations equal, so a gain here can come only
from the uniform 16-bit samples' own slack against the cells' narrowing. That is not learned
structure, and it is never read as such. The word is spelled at 3 bits per tick, without §11's
near-return, whose period-1 cycles (§13) would describe the same sparse crossings.

[measured] **The reading** ([receipt](receipts/2026-10-10-acoustic-release/CELL_INTERVAL.v1.json)):
228710618817 ns against a projection of 110 to 190 s (deadline 300 s). The projection's upper end
was exceeded, and that is reported as its error. Gate 1 is ok. Every sample of every ring lay inside
its cell's interval, so the code is lossless and `R_source = 0`.

| ring | word bits | index bits | total | against `1498880` |
|---|---|---|---|---|
| 0 | 281040 | 1489416 | 1770456 | `+271576` |
| 4 | 281040 | 1464248 | 1745288 | `+246408` |
| 8 | 281040 | 1422112 | 1703152 | `+204272` |
| 12 | 281040 | 1360269 | 1641309 | `+142429` |
| 16 | 281040 | 1267860 | 1548900 | `+50020` |
| 20 | 281040 | 1199937 | **1480977** | **`−17903`** |

- **The cells narrow the sample more as the ring turns faster.** Ring 0's cells leave about 15.9 bits
  per sample (`1489416 / 93680`); ring 20's leave about 12.8 (`1199937 / 93680`). No tick of any ring
  had a single admissible value.
- **Ring 20 meets the inequality**, by 17903 bits. By the rule fixed at launch, this is the cells'
  narrowing against the uniform 16-bit samples' slack, at a word cost spelled at 3 bits per tick. It
  is not learned structure and not compression of the speech's content. It shows that the ring's own
  dynamic symbols, its cells, carry part of the source's information at a cost below what they
  narrow, through one exact inverse.
- **What it settles for the architecture.** §15's decoder works losslessly through one ring's cells,
  with nothing authored. Its lengths are dominated by the index, the within-cell position. The
  next law must narrow that further from the ring's own dynamics: a finer section grain than the
  quarter turn (more rays) or a pair of rings read jointly (the helical duplex, where one ring's cell
  constrains the other's), each paid in the word. The finer grain is the cheaper join, because
  `dynamic_section`'s `RAYS` is already the declared grain of the section chart.

## 17. Refinements to §15 (the source reviewer, via Codex)

The source reviewer found §15's one-ring, source-inverse and repair direction aligned with the
recovered history, and refined it.

1. **The inverse from the emission.** The full emission determines the rate, `ω = −Y e / 2`, so
   `a = [M (ω + r′_ω − r_ω) − 2C w + h K u] / h` with `M = 2C + (h/Y) I + hD + (h²/2) K`. This is the
   same tick as `inverse_step`, read from the emission instead of the velocity. The declared
   operands, the initial state and the carry constraints stay at the consumer. Unknown operands,
   state or carries need an explicit preimage fibre. That one retained state suffices for the ring's
   future is not a reconstruction of past forcing: the inverse uses the before-and-after relation and
   its reached carry.
2. **A candidate certificate (the reviewer's, untested here).** With `h = 1`, `C = I`, state and rate
   on `2^(−32)`, the displacement and velocity splits' remainders zero, and a declared `M = m I` with
   `m < 7`: `|a − a₀| < 7 · 2^(−32) < 2^(−16)`. At the PCM grain `2^(−15)` the nearest incident
   amplitude is then unique. It is neither an implemented inverse nor a validation of
   `inverse_step`, and it says nothing of the summed and rendered file.
3. **A coarse state's residual.** When the decoder knows the state only coarsely, `R_source` includes
   the feedback carry's difference, not only `Δ_T(s − ŝ)`. The initial section class, lift, clock and
   placement are decoder operands or unresolved fibre in the bridge to the repair owners, not
   bookkeeping to drop. `R_source` stays distinct from `R_bank`.
4. **Where the source interface joins the recovered encoder.** `Encoding::found`'s squares,
   `D E = ρ`, `E T = U E` and `E B = J`, must hold with the actual source-reading forms. The
   historical `ExactPhaseCurrentSection` (its phase polynomials and placement carry) and the exact
   PCM butterfly are the reusable laws (recovery in progress).
5. **The cost correction stands.** 2455192 bits include the quadrature's 112076; without them,
   2343116, which is still more than 1498880. The repaired clock keeps its source GO, and its codec
   failure stands. §16's margin is the scoped slack measurement, not learned source content.

## 18. Corrections on the source review of `11142433` and `3e1c051d`

1. **A charted solve has no inverse here.** `inverse_step` admitted a charted solve and returned
   `M z`. With a charted forward `z = X q` the drive error is `(M X − I) q / h`. The reviewer's witness:
   `M = (145/32) I` on the word lattice `(0, 0, 32)`, where the zero chart is admitted, a unit drive
   from rest leaves the state at zero, and the inverse returns zero. **Closed:** a charted solve is
   refused, typed, as `WavePort` already refuses it, and the exact inverse is claimed for the exact
   solve only. Test: `the_inverse_refuses_a_charted_solve_and_an_unlawful_carry`.
2. **The carry contract was not checked.** A rate remainder of the right width with empty state
   parts panicked, and a wrong width silently became zero. **Closed:** each remainder set is either
   empty (all zero) or has the ring's width in all three parts, refused otherwise before any index is
   read. Under the exact law every remainder must be zero. On a lattice, which `inverse_step` now
   takes, every remainder is at most half a unit and every state entry lies on the lattice. The
   displacement identity alone did not validate an arbitrary carry.
3. **§16 overstated what was built.** `interval_pass` computes each sample's interval containment and
   an estimated length. It emits no index code, runs no independent decoder, and does not call
   `inverse_step`. The words "decodes losslessly" and "`R_source = 0`" in §16 claim a consumer that
   does not exist. **Corrected:** §16's valid result is the containment, every sample inside its
   cell's widened interval, and the **estimated** lengths in its table. The consumer is the next
   join: the encoder emits the class and index code as bytes; an independent decoder starts from the
   declared rest state, reads them, recovers each sample, and forward-ticks to regenerate the state
   and carry; and exact equality with the source and the charged length of the emitted bytes,
   including termination and metadata, are checked on the same bytes. The one-value widening is
   coherent for this family (`m < 7`, `δ = 2^(−32)`, `h = 1`: a boundary error under `7/2^17 < 1`
   PCM integer), a certificate still unimplemented. Ring 20's estimated `1480977` against `1498880`
   remains uniform PCM slack.

## 19. The emitted cell codec and its independent decoder (§18's consumer; reading fixed before the full run)

[definition; agent-inferred, October 10] `codec_encode` and `codec_decode` in
`examples/acoustic_release.rs`.

- **The encoder's bytes.** A header (the ring's index, 5 bits; the sample rate, 32 bits; the tick
  count, 32 bits). Then, per tick, the next state's cell (3 bits: class 0 to 3, or 4 for the origin)
  and the sample's index in that cell's interval (`⌈log₂ count⌉` bits). The bits are packed into
  bytes and the last byte is zero-padded. Termination is the declared tick count.
- **The decoder.** It reads only the bytes and the declared ring of the header. It starts at the
  declared rest state on the lattice `2^(−32)`. Per tick it computes the interval from its own state
  (`cell_interval`, the same function the encoder uses, reading only the ring, the clock and the
  state), reads the cell and the index, and recovers the sample. It then forward-ticks the port,
  which regenerates the state and its carried remainders. It checks that the regenerated state lies
  in the cell it read, and that the ring's inverse tick (`inverse_step` on the lattice, with the
  carried remainders) returns the sample.

**The consumer equation.** `codec_decode(codec_encode(x)) = x` exactly, on every sample. The charged
length is `8 · bytes`, header and padding included, against `16 · N`.

**Development read.** Ring 20 over 2000 ticks, 9436104373 ns: 3504 bytes, which is 28032 bits against
32000. The decode is exact, and the cell and the inverse tick held at every tick.

**Reading rule (fixed before the full run).** The full run over the 93680 recorded ticks reports the
emitted bits against `1498880` and the exact equality. As in §16, a margin below `16 · N` is the
cells' narrowing against the uniform samples' slack, reached by the ring's own dynamics through one
exact inverse. It is not learned structure, and it is never read as compression of the speech's
content.

[measured] **The full run** ([receipt](receipts/2026-10-10-acoustic-release/CELL_CODEC.v1.json)):
441252911580 ns against a projection of 442 s (deadline 480 s), with a peak resident set of 13672 KiB.
Gate 1 passed at `ec1b950a`.

- **The consumer equation holds.** `codec_decode(codec_encode(x)) = x` on all 93680 samples. At
  every tick the regenerated state lay in the cell read, and the ring's inverse tick returned the
  sample.
- **The charged length.** 185131 bytes, which is **1481048** bits with the header and padding
  included, against `16 · 93680 = 1498880`: `17832` bits fewer. §16's estimate of 1480977 differs by
  71 bits, the 69-bit header and 2 bits of padding.
- **What it is.** The source decoded exactly from one declared ring's own cells and the sample's
  index within them, at a length 17832 bits under the uniform 16-bit samples. By the fixed rule this
  margin is the cells' narrowing against the uniform samples' slack. It is not learned structure and
  not compression of the speech's content. It is §15's architecture working end to end, at its
  consumer, on the recording: source, cells and index, exact decode, nothing authored. The decode is
  the recording itself, so there is nothing new to hear.

## 20. A finer section grain: the octant (reading fixed before the run)

[definition; agent-inferred, October 10] The quarter-turn cell leaves the in-cell index dominant
(§19). The cell gains one exact sign test, whether `|w′| ≥ |u′|`. With the class's signs `(s_w, s_u)`
this is `s_w w′ − s_u u′ ≥ 0`, one more half-line on the sample, read by the same affine image. It
costs one more bit per non-origin tick in the word (the origin carries none). The header carries a
one-bit flag, and the decoder checks the octant it read as it checks the class. This is a finer
section chart, still exact by signs, and declared like `RAYS`; it is not learned.

**Reading rule.** The octant pays when its narrowing exceeds its bit. That is read as the emitted
length at the octant grain against the quarter-turn grain on the same ring and ticks, with the
decode exact in both. Neither length is read as learned content. Both are the section chart's
grain against the uniform samples.

[measured] **The octant pays** ([receipt](receipts/2026-10-10-acoustic-release/OCTANT_CODEC.v1.json)):
464561780139 ns against a projection of 465 s (deadline 480 s). Gate 1 passed at `39304646`. Ring 20
over the 93680 ticks emitted 170537 bytes, which is **1364296** bits with the header and padding,
against the quarter-turn cell's 1481048 and the samples' 1498880. That is 116752 fewer than the
quarter turn and 134584 fewer than the samples. The decode is exact on every sample, and the cell
(class and octant) and the inverse tick held at every tick.

The quadrant's two sign tests often leave the interval open on one side. The octant's mixed test
`s_w w′ − s_u u′` closes it, which is why one bit buys more than one bit's narrowing. The margin is
still the section chart's grain against the uniform samples, not learned content. §21 takes the
grain's limit as the principle: refine the cell by mediants until the sample is determined.

## 21. The sample as the ring's phase address (acceptance fixed before code is run)

[definition; agent-inferred, October 10] §20's octant is one step of a refinement whose limit is the
principle. Every exact sign test that refines a cell is a line through the origin of the phase plane,
and the lines through the origin are ordered by slope. Refining by mediants walks the Stern–Brocot
tree: the Farey address that the elementary objects give the pair contact's lock. For the next state:

- Its exact image `(w′, u′) = (w₀ + w_m x, u₀ + u_m x)` is read by two exact-law steps of the ring
  owner. Testing the image, not the rounded carry, makes every bound exact: no widening, so the
  descent can end at one value.
- Its class is its quadrant (3 bits). Within the class, its slope `σ = (s_u u′)/(s_w w′)` descends the
  Stern–Brocot tree. At node `p/q` the bit is `σ ≥ p/q`, the exact half-line `q s_u u′ − p s_w w′ ≥ 0`
  on the sample.
- The descent stops when one PCM value remains, and both sides stop at the same node. The bits are
  the ring's phase address to the grain the sample needs.
- A **still line**, `u₀ w_m = w₀ u_m`, is the ring at rest among others. There the slope does not move
  with the sample, so no descent is read and the remaining index is coded. Coding the remaining index
  also covers a descent that reaches its cap of 256 nodes.

**Acceptance.**
- **F1.** `phase_decode(phase_encode(x)) = x` on every sample, with the ring's inverse tick checked at
  every tick.
- **F2.** The emitted bits are reported in their three parts (class, Farey path, index) against
  `1498880` and against §20's 1364296 on the same ring and ticks.
- **F3.** The path's length per tick, as a distribution read in the receipt.
- **Reading rule.** As in §16, §19 and §20, a margin against the uniform samples is the section's
  grain, not learned content. What §21 adds is that the code is made of nothing but the ring's own
  dynamic symbols (its class and its Farey phase address) wherever the line moves.

## 22. The order of the next loops (decided from the mathematics, October 10)

[definition; agent-inferred] The codec's emitted symbols (the ring's class and its Farey phase
address) are codes produced by the field's own dynamics. By guard 9 they are the lawful way into the
field: a sample never becomes `Encoded`, but a section word may be located. The order follows.

1. **The section word through the located route, into the repair owners.** The route is
   `FrameFamily::locate → PassageChart::located → Encoding::found → Encoded::through`, then
   `hnn::keys::PairLocation` and `repair::{key_code, residual_code, reopen}`. The squares
   `DE = ρ, ET = UE, EB = J` hold on the located chart, where the injection is empty. The consumer is
   the codec, with the class bits replaced by the word's key and residual. Acceptance:
   - `reopen = word`;
   - `through` admits the chart, with `check_step` on every stepped lift;
   - exact decode;
   - the charged length reported against the fixed-grain codec.
2. **The ring's material learns from the code length.** The comparison is the next epoch's length.
   Its smooth face is the log of each interval width, whose endpoints are roots of half-lines affine
   in the image. The step is a certified deposition on the ring's own material, made epoch by epoch
   from decoded data only, so the decoder replays it and the decode stays exact. Acceptance: on
   unseen later epochs, the depositing ring's emitted bits are strictly below a never-depositing
   twin's, with the decode exact.
3. **The joint credit of those deposits.** It is `[f_s f_r; g_s g_r]` over the prospective epochs,
   through the material branch's prospect, schedule and cycle owners. Acceptance: agreement with the
   actual depositing run's forward perturbation to second order.

§21's finer grain does not by itself establish the learning join; it supplies the word that loop 1
locates. Loop 2 needs loop 1's length as its comparison, and loop 3 needs loop 2's `g`.

## 23. Loop 1's design, from the owners' actual interfaces (acceptance fixed before code)

[definition; agent-inferred, October 10] **The route.**
1. A near-return window's cycle, its advances as classes `Δℓ + 2 ∈ {0, …, 4}`, repeated over the
   window, is a periodic passage.
2. `FrameFamily::pairs(bound).locate(5, [passage])` reads it on every declared two-ring frame, and
   `FrameLocation::period` returns the located period.
3. A carrying frame's location gives `PassageChart::located`, then `Encoding::found`, then
   `Encoded::through`. The squares `DE = ρ, ET = UE` hold by construction, and `EB = J` holds with an
   empty injection.

**The defects are substitutions, not erasures.** `compression::keys::repair` repairs *erasures*
consistent with the located relation (`DamagedPassage::encoded`; `residual_code` refuses a truth that
leaves its family). A near-return's defect *breaks* the relation: the cycle predicts one advance, and
the word holds another. So the defects do not enter the repair owner as erasures. They are the helical
code's substitutions, "absorbed iff the reached difference lies in the kernel" (elementary objects,
the helical code). The residual is the defect list itself, its positions and advances, and the decoder
reopens by `transport.regenerate(key, L)` followed by the substitutions.

**The cost, stated before measuring.** A located transport is described by its frame (an index in the
family), its key (a lift on `ℤ/D`) and its per-class digits. That is at least `5 ⌈log₂ D⌉` bits, more
than the cycle spelled out at `3τ` bits whenever `τ` is short. §13 measured that most of this speech's
cycles have period 1. The located route will therefore **not** shorten the code on this recording, and
that will be measured, not assumed. What it buys is the join: the word enters the field as `Encoded`
through the located chart, which loop 2's deposition needs. A sample never enters the field, and a
located section word may.

**Acceptance.**
- **W1.** For every admitted near-return window whose cycle a frame carries, `Encoded::through`
  admits the located chart, with the squares checked by the owner and `check_step` on every stepped
  lift.
- **W2.** `regenerate(key, L)` with the defects substituted equals the window's word exactly.
- **W3.** Per ring: the windows located, the windows no frame carries (each typed: narrow, empty,
  plural, open), and the located description's bits against the spelled cycle's, as exact integers.

## 24. Loop 2's acceptance: the ring's material learns from its own code length (fixed before code)

[definition; agent-inferred, October 10, with the reviewer's two design checks] The codec of §19 and
§20 is fixed-material: the ring's `K` (its turn) and its port coupling `a` (its memory) are declared.
Loop 2 lets the ring's own material move by deposition, epoch by epoch, so that the cells narrow the
samples more. Its comparison is the codec's own length, its law is the existing certified deposition,
and its decoder replays every deposit.

- **The comparison.** Over an epoch, the emitted bits are `Σ_n (cell bits + ⌈log₂ count_n⌉)`. The
  smooth face is `Σ_n log₂ (hi_n − lo_n + 1)`, whose endpoints are the roots `−a/b` of half-lines
  affine in the image `(w₀, w_m, u₀, u_m)`. Those depend on the material through the ring's step.
  The learning covector is `d(face)/d(material)` through the step's tangent in the material (the
  `f_r` block), read along the epoch.
- **The law.** The certified step on the ring's own material (`K`, and the port coupling through
  `Y`), committing at least one lattice unit or refusing (`DeclaredStepRefusal`).
- **Causality (the reviewer's check 1).** The deposit at the end of epoch `k` reads only samples the
  decoder has already decoded in epochs `≤ k`. The shared initial material, the epoch length and
  every choice the step makes (its exponent, its family) are either declared context or charged in
  the bits. Nothing is chosen from future data and then left out of the code. The decoder replays
  each deposit from its own decoded samples, and the decode stays exact.
- **The twin (the reviewer's check 2).** The same codec with the material held fixed. The comparison
  is the total emitted bits, with the charged side information included, and the exact
  reconstruction of both. The receivers' local criteria (each epoch's length, each ring's) are
  reported apart, never collapsed into one reward.

**Acceptance.**
- **A1.** `decode(encode(x)) = x` for the depositing codec, with every deposit replayed.
- **A2.** On the recording's later epochs, which no deposit has read before it is coded, the
  depositing ring's emitted bits against the twin's, epoch by epoch, as exact integers. Learning is
  claimed only where the depositing ring is strictly below the twin, net of its charged side
  information.
- **A3.** Every refused step is typed and reported, never answered by a larger step.
- **A4.** The joint credit of the deposits is loop 3's. Here the deposit admits on the next epoch's
  measured length only. No `g_s` or `f_r` beyond one epoch is claimed.

## 25. Measured: loop 1's W1 and §21's phase address

[measured] ([receipt](receipts/2026-10-10-acoustic-release/LOOP1_AND_PHASE_DEV.v1.json); developer
reads.)

- **W1 is not met.** The ring `t = 1` under the replica's F1, in its settled window, near-returns at
  `τ = 7` with no defect (27 bits against 360). Its cycle of advances, as 5 classes repeated over the
  window, is carried by none of `FrameFamily::pairs(9)`'s 38 declared two-ring frames: 13 are
  narrow, 13 empty, 12 plural, and none carries it. This is the tone record's §2 finding: a generic
  word is located on no single declared helix. W2 is vacuous. The first test asserted a carrying
  frame and failed. It now pins the typed reading. The declared family's bound is **not** widened
  after the failure: the next subject is why a 5-class period-7 cycle is plural or empty on every
  pair frame, read from the typed fibres.
- **The phase address is exact, and a worse code than the octant.** Over 2000 ticks of ring 20 it
  emits 26560 bits: 6000 class, 20458 Farey path, 30 index for the still lines, plus header and
  padding. On the same ticks the octant emits 24440 and the quarter turn 28032. A mediant descent
  splits the slope space, not the sample's interval, so each Farey bit narrows less than an index
  bit: about 10.2 path bits per tick against the octant's about 8.2 index bits. No full run is made,
  because the comparison is settled. What §21 shows is narrower: the sample can be coded by nothing
  but the ring's own dynamic symbols wherever its line moves, at a cost this measurement reads.

## 26. Loop 1's W1 and W2 met, after correcting my adapter

[measured] ([receipt](receipts/2026-10-10-acoustic-release/LOOP1_LOCATED_WORD.v1.json).) §25's
failure was in **my adapter**, not in the route. I declared all five advance classes as the alphabet,
but location reads only equality: its relabelling law (`compression::keys::transport`) says each
frame's reading on `π ∘ x` is its reading on `x`. The tone route accordingly reads its samples as
ordinals in order of first occurrence. The ring `t = 1` under F1 turns so that its cycle shows only
**two** advances (`Δℓ = +1` and `−2`), so 13 frames were narrow only because of my declaration.

With the cycle read as its own ordinals, the frame family and its bound unchanged (`pairs(9)`, 38
frames):

- **Clean tone.** `τ = 7`, 0 defects. **18 of 38** frames carry the cycle, and the other 20 are empty.
  On every carrying frame the located chart is founded and admitted (`Encoded::through`), the
  squares hold, every stepped lift passes `check_step`, and `regenerate(key, L)` equals the window's
  word exactly. W1 and W2 are met.
- **Departed tone** (one sample raised by 7 after the settle allowance). `τ = 7`, 6 defects. The same
  18 frames carry the cycle, and `regenerate(key, L)` with the 6 defects substituted equals the
  window's word exactly.

`acoustic_encoding` passes 8 of 8. **Narrowed** (Codex's review of `f06ff2b0`):
- The test checked the located chart through `Encoded::through` against a wide one-ring field
  (`wide_field`, period 16), not the located two-ring helix. It never called `Field::admit` or
  ingestion, so neither field entry nor deposition's consumption is established by §26.
- Its decoder recovered the advance word only (`Δℓ + 2`), not the section word's start class,
  crossings, placement and clock.
- It checked the base cycle's lifts and then substituted the departures; the departed passage itself
  was never admitted.
- What §26 establishes: the observed cycle's chart (its own ordinals, a support restriction and
  relabelling, not a permutation of five classes), the located regeneration of the cycle, and the
  advance word with its substitutions. No key is forced and the family is not enlarged: 18 frames
  carry and 20 are empty, of the same 38.

§28 builds the consumer.

## 27. W3: the recording's windows through the located navigator's own code (reading fixed before the run)

[definition; agent-inferred, October 10] The transport owner already has an actual code for a located
navigator, `located_code` and `read_located` (`compression::keys::transport`). It writes the transport
per receiving cell, the labels, the key, and the **patches** where the word departs from the
regeneration, which are exactly §23's substitutions. The owner prices them, not this record.

For each admitted near-return window of a ring:
1. The cycle, read as its own advances' ordinals, is located on `FrameFamily::pairs(9)`.
2. On every carrying frame whose shape the code admits (its cells equal the classes), the window's
   *actual* word is coded by `located_code`, and `read_located` must return it exactly.
3. The located length is the shortest such code, plus the frame's index (`⌈log₂ 38⌉ = 6` bits) and
   the ordinal map (3 bits per class).
4. Each window is counted as located, carried but shape-refused, or not located.

**Reading rule.** The located bits are reported against the same windows' spelled near-return bits.
§23's expectation stands: for short cycles the located description is the longer one. The route is
claimed as a join and never as compression unless the located bits are strictly fewer.

**The development read** (ring 20, the recording's first 2000 ticks, debug binary, one thread). It read 16
windows: 4 located, 0 shape-refused, 12 not located. The located bits were 235 against the same
windows' spelled 224, so on these windows the located description is the longer one, as §23 expected.
Wall time was 3858294942 ns, peak RSS 13836 KiB.

### 27a. The full read was INCOMPLETE at its deadline, and the projection error

The full read ran rings 0, 8, 16 and 20 over all 93680 recorded ticks, one thread each.
- It was projected at about 200 s from the development read's 1929147471/1000 ns per tick.
- Its deadline was fixed at 300 s.
- It stopped at that deadline: exit 124, wall 300001503956 ns, child peak RSS 20044 KiB.
- **INCOMPLETE.** No ring's result was read.

The last progress lines:

| Ring | Ticks | Elapsed | Slowest measured interval |
|---|---|---|---|
| 0 | 88620 | 34006 ms | 3028 ms over 7596 ticks |
| 8 | 88059 | 59777 ms | 9342 ms over 7897 ticks |
| 16 | 88023 | 139762 ms | 18298 ms over 8029 ticks |
| 20 | 64008 | 243049 ms | 32906 ms over 8001 ticks |

**Two causes, both mine.**
1. **The projection came from an unrepresentative unit.** A window's cost depends on whether it is
   located: locating means trying every carrying frame and coding and reading back the word.
   - In the recording's first 2000 ticks, 12 of 16 windows were not located.
   - The voice later locates more of its windows. Ring 20's 64008 ticks took 243049 ms, against
     the development read's projection of 15435108915471/125 ns for that count. That is the
     projection error, recorded as such.
   - A development read for a content-dependent unit must be taken where the content is, or
     projected from the slowest measured interval.
2. **The driver withheld finished results.** It printed every ring's result only after all rings
   joined. Rings 0, 8 and 16 were past their last chunk line by 139762 ms, and at most 5657 ticks
   remained in each. Their results were still lost with the process.
   - [agent-inferred] Repaired: each ring prints its result when its own pass ends, so a deadline
     stop keeps the rings that finished.

**The next read changes what is declared, not the limit.** Its deadline stays at 180 s, and it runs
two processes, 4 threads in all:
- rings 0, 8 and 16 over the whole recording;
- ring 20 over its first 40000 ticks.

Each projection is the full read's measured elapsed at its last progress line, plus the slowest
measured interval's rate over the ticks that remain:
- ring 16: 139762 ms plus 5657 ticks at 18298/8029 ms per tick, about 153 s;
- ring 20: 122678 ms to tick 32004, plus 7996 ticks at 32906/8001 ms per tick, about 156 s.

Ring 20's whole recording projects past three minutes at its measured rate. It is declared on a
prefix and is not relaunched whole.

### 27b. Measured: the declared split read (developer read)

Both runs finished inside the fixed 180 s deadline
([receipt](receipts/2026-10-10-acoustic-release/W3_LOCATED_WINDOWS.v1.json)):
- (a) wall 146513953189 ns against the projection's 175094412/1147 ms, peak RSS 13836 KiB;
- (b) wall 158126089092 ns against 1244663054/8001 ms, peak RSS 18804 KiB. Run (b) overran its
  projection by less than 2563 ms. That is a projection error; the deadline held.

| Ring | Ticks read | Windows | Located | Shape-refused | Not located | Located bits | Spelled bits, same windows |
|---|---|---|---|---|---|---|---|
| 0 | 93680 | 147 | 0 | 0 | 147 | 0 | 0 |
| 8 | 93680 | 606 | 0 | 0 | 606 | 0 | 0 |
| 16 | 93680 | 1932 | 84 | 0 | 1848 | 6766 | 7557 |
| 20 | 40000 | 783 | 78 | 2 | 703 | 4752 | 3978 |

**Reading, by §27's rule.**
- **Ring 16:** the located code is strictly shorter on its 84 located windows, by 791 bits. Over the
  ring's 1932 windows that is no compression: a flag naming which windows take the located code costs
  more than 791 bits (one bit per window is 1932 bits).
- **Ring 20:** the located code is longer on its 78 located windows, by 774 bits, as §23 expected
  for short cycles.
- **Rings 0 and 8:** no window was located. Their longer windows carry cycles that no declared pair
  frame carries.

The route is a measured join on 162 of the 3468 windows read. It is not a compression of the
recording.

## 28. The departed section word through the field on its located helix (acceptance fixed before code)

[definition; agent-inferred, October 10] This replaces §26's test, on the same tone, ring and window:
F1, `t = 1`, window `(120, 120)`, clean and with the one departure.

**The passage.** The dictionary is the actual word's advances in order of first occurrence, so every
departure's advance is a class. The passage is the actual word's ordinals. The cycle is the
near-return's, read in the same dictionary.

**Acceptance, for each tone.**
- **F1, field entry.** Every frame of `FrameFamily::pairs(9)` that carries the cycle founds the
  *actual* passage, departures included, through the located chart (`PassageChart::located` opens it
  at the key with the fewest patches). The passage is then:
  1. encoded on `field_on(helix.periods())`;
  2. admitted by `Field::admit`;
  3. ingested by the reference port (`Reference::mount` at rest, then `ingest`), which consumes all
     `L` cells or reports its carry-out with the cells it consumed.

  At least one frame carries.
- **F2, the pair at the ring's own distance cap.** The menus read distances `δ ∈ [1, d − 1]` on the
  receiving ring of period `d`. `pairs(9)` already declares receiving periods 8 and 9, so the family
  is not widened. On each carrying frame with `d > τ`:
  - the pair location (`PairLocation::open` on the receiving ring, observing `damaged_station_pairs`
    of the admitted passage with its departure cells erased) locates a pair `(δ, f)`;
  - its key is priced by `key_code(relation, d)`;
  - the restriction releases every erased departure cell to the cycle's class.

  The repair therefore returns a departure to the cycle: `residual_code` of the actual word is
  refused `NotRegenerated` on the departed tone, and is empty on the clean one. A substitution is not
  an erasure, and the substitution residual is what carries it. A frame with `d ≤ τ` is reported as
  it is, never answered with a larger family.
- **F3, the whole word decoded.**
  - **The emission:** a header (settle tick and window length, the placement; the ring's declared
    `t` and hop, the clock), the start class (2 bits), the frame index (`⌈log₂ 38⌉` bits), the
    dictionary (3 bits per class), and `located_code(transport, [actual])`, whose patches are the
    substitution residual.
  - **The independent decoder** reads only the emission and the declared family. It takes the frame
    by its index, the ordinals by `read_located`, the advances through the dictionary, and the
    classes and crossings by `dynamic_section::land` from the start class.
  - **What must hold:** the decoder returns a `SectionWord` equal to the window's, every symbol's
    class, advance and crossing, with equal `winding()`, and the header's placement and clock read
    back equal.
- **Where F2 and F3 sit** (derived before the run from the owners' laws). `located_code` ranks a
  bijection: the receiving cells must equal the classes (`shape_refusal`). F3 is therefore read on
  the carrying frames whose receiving period equals the dictionary's size. F2 needs `d > τ`, so for
  a cycle of few classes (`τ = 7`, two classes) the two readings sit on different frames of the same
  family. Each is reported on its own frames. A refusal of either is measured and named; it is not
  answered by widening the family or the ceiling.
- **F4, charged together.** The emission's bits, apart from the common header, are reported beside
  the near-return's `L_τ + 2` (with the start class) and the spelled `3L + 2`, with the pair's key
  bits beside them. No compression is claimed unless the emission is strictly shorter.

**What stays unbound.** The section word is the states' quotient by their ray cells. Its fibre is
each state's amplitude and phase inside its cell, and through the inverse tick
(`ResonatorOperands::inverse_step`) the samples. F3 does not decode that fibre, so F3 is not a source
codec. The codec that binds the fibre takes the cell codec's index per tick (§18–§20), with the
cells supplied by the decoded word. It is §29's subject, charged against the octant codec.

### 28, measured: the clean word enters and decodes whole; the departed word is refused by its own chart

[measured] ([receipt](receipts/2026-10-10-acoustic-release/S28_SECTION_WORD_FIELD.v1.json); developer
reads.) `acoustic_encoding` passes 8 of 8 on the third run. The first two runs failed, both in **my
adapter**:
1. I declared the pair's relation over the dictionary's 2 classes. The admitted passage's classes
   are the chart's indices (`Encoded::classes_read`, here 8), so F2 now reads in them.
2. The departed tone then carried on no frame (below).

**Clean tone** (`τ = 7`, dictionary `[1, −2]`, 18 of 38 frames carry, 20 empty):
- **F1 met.** All 18 carrying frames found, encode, admit (`Field::admit` on
  `field_on(helix.periods())`) and ingest the passage through the reference port.
- **F2 met.** On the 4 carrying frames with `d > 7` (`[7, 8]`, `[7, 9]`, `[8, 9]`, `[9, 8]`), the
  pair located from the admitted passage is `δ = 7` with the identity map, the only surviving
  distance. Its key is 35 bits at `d = 8` and 39 bits at `d = 9`. The repair's residual is empty.
- **F3 met.** On the 2 carrying frames with `d = 2` (`[7, 2]`, `[9, 2]`), the independent decoder
  returns the whole `SectionWord` (start class, every class, advance and crossing, the winding)
  with its placement and clock.
- **F4.** The emission after its 28-bit header is 37 bits on `[7, 2]` (located code 20) and 40 bits
  on `[9, 2]` (located code 23). That is against the near-return's `L_τ + 2 = 29` and the spelled
  `3L + 2 = 362`: longer than the near-return by 8 and 11 bits, as §23 expected for a short cycle.

**Departed tone — F1 NOT MET.**
- The six departures are `(60, −1)`, `(61, 0)`, `(62, 2)`, `(63, 0)`, `(68, 2)` and `(75, 2)`.
  Every one is an advance **outside the cycle's support** `{+1, −2}`, so the five-class dictionary
  holds 3 classes the cycle never reads.
- A located member has no transport for a class it never read: its gauge is plural, never guessed.
  The location over five classes is plural on 12 frames, empty on 13 and narrow on 13, and carries
  on none.
- So the departed passage is **not a passage of the cycle's located chart**. Its departures are the
  chart's cokernel, and `Encoded` has no slot for a cell outside its chart. This is no defect of the
  owners: an encoding that admitted such a cell would fabricate its transport.
- The test now asserts the refusal, typed: only a dictionary wider than the cycle's support carries
  on no frame. F2 and F3 are not read on the departed tone.

The failure is §28a's subject.

## 28a. The departed word enters as its runs in the cycle's chart, its departures the residual (acceptance fixed before code)

[definition; agent-inferred, October 10] §28 measured that a departure outside the cycle's support has
no class in the cycle's located chart. The encoding law then fixes how the departed window enters:
- **What enters.** Only the cells the chart has: the window's maximal runs of cells inside the
  support `S`, the cycle's own classes. Each run is a passage opened at its own located key.
- **What does not.** The departures are the chart's cokernel. They do not enter the field; they are
  the residual, each named by its position and its advance in the five advances.
- Nothing is fabricated: every actual chart cell is ingested, and no departure is replaced by a
  chart class.

This differs from §28's F1 in one respect, which the measurement forced: the passage that enters is
the window's runs, not the whole window. The tone, ring and window are §28's, departed.

**Acceptance.**
- **R1, the runs enter.** The dictionary is `S`, the cycle's advances in order of first occurrence.
  The cycle located in `S` must carry on the same 18 frames as the clean tone. On every carrying
  frame:
  - the runs are founded together by `PassageChart::located`, each at its own least key with the
    fewest patches;
  - they are encoded on `field_on(helix.periods())` and each is admitted;
  - the reference port ingests them in clock order, the first opening a moment and each later run
    continuing it.

  A refusal of the continuation is reported typed, and R1 is then not met. The field's clock does
  not advance across a departure: no transport for it is known.
- **R2, the pair.** On carrying frames with `d > τ`, the pair is located from the stations of all
  the admitted runs. Each run's repair residual must be empty, since a run holds no departure.
- **R3, the whole word.** On carrying frames with `d = |S|`, the emission is:
  1. the header, the start class, the frame index and the dictionary;
  2. the departures: `γ(|D| + 1)`, then for each departure `γ(gap)` and its advance in 3 bits;
  3. `located_code(transport, runs)`.

  The independent decoder derives the run lengths from the departures and the window length, reads
  the runs by `read_located`, interleaves the departures, and must return the whole `SectionWord`
  with its placement and clock.
- **R4, charged.** The emission's bits after the header are reported beside the near-return's
  `L_τ + 2 = 75` and the spelled `3L + 2 = 362`.

### 28a, measured: the departed word enters as its runs and decodes whole; §28's F1 corrected

[measured] ([receipt](receipts/2026-10-10-acoustic-release/S28A_RUNS_IN_THE_CHART.v1.json); developer
reads.) `acoustic_encoding` passes 9 of 9.

**A correction to §28's F1, found by this loop.** The reference port's ingest stops after the
occurrence whose step carries the joint clock out, and then refuses any further cell until
`close_aeon`. §28's check accepted that stop as entry, so its "ingested" covered only the cells up to
the first carry-out. This loop's first run showed it: on frame `[6, 5]`, after the first run's stop,
the port refused the next run, "the aeon awaits close_aeon".
- Both tests now ingest **whole**: at each carry-out the aeon is closed over the admitted receiving
  phases, and the rest of the passage (`Encoded::part`) continues the same moment.
- The clean tone's 120 cells close **17 aeons** on every one of its 18 frames: the joint clock
  carries out about once per cycle of the located helix.
- §28's F1 is met on that reading, and its other readings are unchanged.

**R1 met.**
- The support is `S = {+1, −2}`. The departures `60, 61, 62, 63, 68, 75` are exactly the cells
  outside it.
- The runs are `[0, 60)`, `[64, 68)`, `[69, 75)` and `[76, 120)`.
- The cycle in `S` carries on the same 18 frames.
- On every one of them, the four runs are founded together, each at its own key, admitted and
  ingested whole into one moment. That closes 14 aeons on 17 frames and 15 on one.
- No departure enters the field.

**R2 met.** On the 4 frames with `d > 7`, the pair located from all the runs' stations is `δ = 7`
with the identity map, the only survivor. Every run's repair residual is empty.

**R3 met.** On `[7, 2]` and `[9, 2]`, the independent decoder returns the whole departed
`SectionWord` with its placement and clock.

**R4.**

| Frame | Emission after header | Start, frame, dictionary, departures | Runs' located code |
|---|---|---|---|
| `[7, 2]` | 96 bits | 64 | 32 |
| `[9, 2]` | 102 bits | 64 | 38 |

The near-return's `L_τ + 2` is 75 bits and the spelled `3L + 2` is 362. The emission is longer than
the near-return by 21 and 27 bits. The departures cost the same in both (position and advance); the
excess is the runs' four keys, the frame index and the dictionary.

**What §28–§28a establish.** A ring's section word, clean or departed, enters the field declared on
its located helix through the actual admission and ingestion owners, across its aeons. Its pair is
read at the ring's own distance cap, and its emission decodes the whole word.
- On this short cycle the located description costs more than the near-return. No compression is
  claimed.
- The amplitude and phase fibre, and through it the samples, stays unbound. That is §29's subject.

## 29. The source codec with its cells supplied by the ring's section word (acceptance fixed before code)

[definition; agent-inferred, October 10] The cell codec (§18–§20) writes, for each tick, the next
state's cell (its quadrant, 3 bits, or the origin) and then the sample's index in that cell's
interval. Within a settled window, that cell is the landing class of the section word's symbol. The
section word therefore supplies the cell stream, and the index is the fibre: each state's amplitude
and phase inside its cell, and through the inverse tick, the sample. This binds what §28 left
unbound, on the recording itself.

**The code.**
- The ring's stream is tiled into blocks of the census window, four of the ring's turns
  (`half_memory`). The last block may be shorter.
- Each block carries one flag bit:
  - **Flag set.** The block opens on a state off the origin, and its section word's near-return is
    admitted. The emission is the owner's `NearReturn::code` (`L_τ` bits); then, per tick, the octant
    bit when the octant grain is declared, and the index.
  - **Flag clear.** Per tick, as the cell codec: the 3-bit cell, the octant bit and the index.
- The start class is not written: the decoder holds the state the block opens on. Neither is the
  window: the decoder derives it from the declared ring.

**Acceptance.**
- **C1, exact.** An independent decoder, given only the bytes and the declared ladder, returns every
  PCM sample exactly. Per tick, the regenerated state lands in the cell it read (from the decoded
  word or from the cell bits), and the inverse tick returns the sample.
- **C2, charged.** Reported together:
  - the emitted bits;
  - the cell codec's bits on the same stream and grain, counted by the encoder from the same
    per-tick widths;
  - the blocks read and admitted;
  - the raw 16-bit PCM.

  The difference from the cell codec is claimed exactly as measured. It is the class stream's
  near-return structure (the ring's own cycles), not learned content, and the indices are unchanged.
- **The read.** Ring 20 (the codec's ring), quarter and octant grain:
  - a development read of 2000 ticks;
  - then a declared prefix of 20000 ticks, projected from that read;
  - the whole recording only by its own stated authorization: the octant codec's full run took
    464561780139 ns.

**Expected from the census** (§11's N3 on ring 20: 2550 of 5222 windows admitted, 127525 bits
against 153000 spelled over them): a saving on the cell stream of a few percent of the cell bits,
less one flag per block. That is small beside the indices. It is stated now so that the
measurement can correct it.

**Development read** ([receipt](receipts/2026-10-10-acoustic-release/S29_DEV.v1.json)): ring 20, the
recording's first 2000 ticks. The near-return tests also assert `|code| = L_τ` and the read-back, and
refuse a code cut short (`LockRefusal::Code`).
- **C1 met at both grains.** The decode equals the source exactly.
- **C2 at the quarter grain:** 28072 bits emitted against the cell codec's 28029.
- **C2 at the octant grain:** 24479 against 24436.
- At both grains 12 of the 100 blocks are admitted. Their words take 663 bits in place of 720 cell
  bits, and the 100 flag bits outweigh the 57 saved. On this prefix the code is 43 bits longer than
  the cell codec.

The census's whole-recording admission is higher (2550 of 5222 windows), so the full read decides C2.

### 29, measured: the section word's cells shorten the whole recording's code exactly

[measured] ([receipt](receipts/2026-10-10-acoustic-release/S29_FULL.v1.json); developer read at
`f7dd904dc`.) The run was announced with its grounds: the workload, the measured upper cost, the
debug build's exact rational step as the bottleneck, and the new information it would establish. It
covers ring 20, all 93680 recorded ticks, at both grains, as two concurrent processes.

- **C1 met at both grains.** The independent decode equals the source exactly. At every tick the
  regenerated state lands in the cell read, and the inverse tick returns the sample.
- **C2:**

| Grain | Emitted, before padding | Cell codec, same stream and grain | Difference | Raw PCM |
|---|---|---|---|---|
| quarter | 1461697 | 1481047 | 19350 fewer | 1498880 |
| octant | 1344943 | 1364293 | 19350 fewer | 1498880 |

- At both grains, 1899 of the 4684 blocks of 20 ticks are admitted. Their words take 89906 bits in
  place of 113940 cell bits, and the flags cost 4684 bits:
  `113940 − 89906 − 4684 = 19350`.
- The byte-padded emissions are 182713 bytes (1461704 bits) and 168118 bytes (1344944 bits). The
  published cell codec runs emitted 185131 bytes (1481048 bits) and 170537 bytes (1364296 bits).
- **Time.**
  - Quarter grain: wall 456191187415 ns, peak RSS 13268 KiB.
  - Octant grain: wall 476984164367 ns, peak RSS 13872 KiB.
  - The projection was `93680/2000 × 10122472169` ns. The octant run passed it by less than 3 s,
    inside the fixed 500 s deadline: a projection error, recorded.

**Reading.** On the whole recording, the ring's section word supplies its own cells in fewer bits than
the cell codec spends on them. The code is strictly shorter, by 19350 bits at each grain, and the
decode is exact. The census predicted a reduction of this order (§29's expectation), and on the first
2000 ticks the flags outweighed it (development read).

**Scope.**
- The reduction is the class stream's near-return structure: the declared ring's own cycles, read in
  the declared window, measured on encoder-produced bytes.
- It is not learned content. No material moved, and the index of every sample, which is the fibre,
  is unchanged.
- It binds the section word to the source. The cells inside an admitted window are the word's
  landings, and the samples follow by the cell's interval and the inverse tick.
- Loop 2 (§24) is where the ring's material would learn from this length.
