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

- **The voice's rings now return.** Ring 0 admits 172 of its 173 windows (exact locks: 5), described
  in 43991 bits against 326112, with 3284 defects kept. Rings 1–5 admit 203, 233, 279, 328 and 384
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
