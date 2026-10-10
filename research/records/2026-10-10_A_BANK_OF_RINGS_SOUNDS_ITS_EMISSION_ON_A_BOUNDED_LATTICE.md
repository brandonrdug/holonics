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
  that keeps every `|q_n| ≤ 2^15 − 1`: a normalization at the exterior boundary, read from the
  emission's own peak.
- **A3, the stream is one.** Receiving the recording in chunks leaves the same states, remainders and
  render as receiving it whole.
- **A4, the output.** A 16-bit mono file at the recording's rate: the recording's length followed by
  one second of continuation (incident `a = 0`, the rings emitting what they hold).

**Not claimed:** that the bank is learned or located (it is declared, §2); that anything is
generated, predicted or recognized; any quality or fidelity reading. The output is the bank's
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
