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
