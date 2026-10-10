# A matched wave enters a loaded ring, and its state crosses its own section

**Date.** October 9. **Issues.** #148, #73, #386, #62. **Grade.** Native build of items 1–3 of the
second rung's native list, against numbers read from an independent exact replica. Each claim carries
its grade. The Rust was compiled and run once by a delegated worker under the common compiler lease
(commands and times in [`native_runs.txt`](receipts/2026-10-09-acoustic-native/native_runs.txt)); that
is a worker's reading, not a validation-queue receipt.

## 1. The question, and the acceptance fixed first

[source-inspected] The second rung is a design plus an exact replica (a record at commit
`35d5951634ab` of another branch, not on main, so no link): a sampled sound enters as a
**wave at a ring's port** (not as a symbol sequence), the ring continues across the stream, and the
sound's dynamic symbols are the **ring's own section crossings**. Its §8 lists nine native terms. This
record builds the first three and nothing else: a matched-source wave at a loaded ring's port distinct
from `Encoded`; the ring's state carried across the stream; and the reader of the signed crossing of the
ring's own state through its section rays, with the lift carried. The lock reader (§8 item 4), the joint
period, the amplitude receipt, the gauge, the render and the pump are not in it (§9).

[project-postulate] The acceptance was written into
[`tests/acoustic_wave_port.rs`](../../crates/holonics/tests/acoustic_wave_port.rs) from the replica's
printed numbers
([`replica_probe_output.txt`](receipts/2026-10-09-acoustic-native/replica_probe_output.txt), read by
[`replica_probe.py`](receipts/2026-10-09-acoustic-native/replica_probe.py) from the acoustic-locks
replica `6d96dfcc…`, which is not a repository owner) before the first run. The ring is the replica's
declared one, `t = 1`, `C = 1`, `D = 0`, `K = 4(a² + t²)`, `Y = 1/(4a)`, `a = t/8`, `h = 1`, driven from
rest by its F1 sawtooth of period 7, `x = (−9, −9, −2, −2, 5, 5, 12)`. The consumer equations:

```text
E′ − E = (hY/4)(a² − b²) − h ω D ω        every tick (ReceivedTick::closes, and again at the test)
(u, w)_n and b_n                          the replica's exact states and reflected waves
state after chunks = state after the whole stream
ℓ_(k+1) = ℓ_k + Δℓ(z_k, z_(k+1)),  z = (w, u)       the replica's symbol word (cls, Δℓ)
arrivals = aeon::epochs of the lift's micro-steps at ClockLift::ring_section(0, 4)
ℓ(−z) = ℓ(z) + 2
```

The step passes only if every item holds exactly. Two items were added after the first run and are
marked: the opposite-ray form of the polarity item (§4.5) and a probe of the strand question (§6).

## 2. The owners, and the concrete missing term

[source-inspected] A search hit is not a join. Each row names the owner and the term it lacked.

| Step | Existing owner | What it does | Missing term | Built |
|---|---|---|---|---|
| The ring tick | `hnn::ring::{ResonatorMaterial, ResonatorOperands::step, ResonatorStep::closes}`; Lean `HNN/Ring.ring_tick_executed_energy_balance` | The executed unpumped tick `M ω = 2Cw + hβ − hKu`, `u′ = u + hω`, `w′ = 2ω − w`, `out = β − (2/Y)ω`, with the port balance | A continuing drive: `step` takes a drive and a state per call, and its producers are a `Word`'s junction output; the mode state is word-local | `WavePort` |
| A wave at the port | `hnn::word::world_boundary` (`admit_source_boundary`, `return_source_wave`) | Books `hY(|b|² − |a|²)/4 = −W_World` against an actual co-clock World's state at an *unloaded* source port; refuses a loaded ring | A **non-participating** matched source: a recording's incident wave comes from a chart, and its reflected wave is absorbed by the matched source | `MatchedWave` (the World's join is unchanged) |
| The entrance | THE_MACHINE guard 9; `hnn::encoding::{Encoded, PassageChart::located}` | "An exterior code (a byte, a code point, a sample, a joint angle) has no path into the field" | The guard does not draw the line between a sample as a **code** (nominal, stays refused) and a sample as a **wave amplitude** (a quantity with a power pairing, admitted at a port by passivity) | two types that do not convert, five `compile_fail` doctests, a bullet in guard 9 |
| The ring's section | `holon::parametron::ring_crossings`; `aeon::{ClockLift::ring_section, epochs, Reading}`; `hnn::ring::{sheets, turn}` | The rotor's integer section arrivals (a declared rate); the aeon's signed flux through a ring section of a lift; the pump axis's half-plane (a sheet, half-turn-blind) | The crossing of a **dynamic** section by the ring's own state `(w, u)`: the signed ray count of a chord and its lift | `SectionReader`, `chord`; the aeon owners are the consumers |
| The lift as a reading | `aeon::Reading` (`of_turns`, windings plus open phase) | Whole windings and open phase of a rational turn count | None: `Reading::of_turns(ℓ/4)` is the lift's reading | consumed |

## 3. What was built, and each choice with its reason

[definition; agent-inferred] **`hnn::wave`** ([`wave.rs`](../../crates/holonics/src/hnn/wave.rs)).
- `MatchedWave { admittance, hop, samples }`: private fields, built from exact amplitudes and a declared
  port and step, never from an `Encoded`, convertible neither way. The gain, origin and exact step of a
  recording are the boundary chart's and declare no meaning; the type carries only the numbers and the
  port they were matched to.
- `WavePort`: the operands of one unpumped, linear, exact ring, the driven real coordinate, the mode state
  `[u, w]` and the clock. `receive(&wave)` is a lazy iterator, one amplitude per tick; the wave is refused
  unless its admittance and step are the operands' (matched). Each tick's balance
  (`ReceivedTick::closes`) is checked before the state is committed; a refused tick leaves the port as it
  was. The port holds nothing that grows with the stream but the state's own bits (§8).
- Reason for the narrow admission: the consumer equation is the unpumped exact one. A pumped, scheduled,
  nonlinear or lattice ring is refused with a typed reason; the pumped port (subharmonic locks, the sheet
  symbol) is the second rung's item 9, owed.
- Reason for width 2: a ring lives on a realified width (two coordinates per node). A mono pressure drives
  the real force of a node; for an isotropic node the quadrature coordinate stays exactly zero (asserted).

[definition; agent-inferred] **`hnn::dynamic_section`**
([`dynamic_section.rs`](../../crates/holonics/src/hnn/dynamic_section.rs)).
- `quadrant`, `chord` and `SectionReader`: the class of `(w, u)` (each of the four quarter-turn rays
  belongs to the class it starts), the signed advance of the lift along a straight chord, and a reader
  that keeps the last state and the lift (the quotient the next tick needs) and returns, per tick,
  `SectionSymbol { class, advance, crossing }`. `reading()` is the lift as `aeon::Reading` (`ℓ/4` turns).
  `half_turn()` is the polarity partner (`−z` at `ℓ + 2`). The origin and a chord through it are refused,
  typed, and a refused tick changes nothing.
- Reason for four rays: the quarter turn is the only finite-order rational rotation of the plane (the
  pump's steps are the same four), so the rays are exact and read by signs; the grain is declared, not
  located (§7).
- Reason the aeon is a consumer and not kept: an `Aeon` is a chain of passages; the streaming reader would
  turn into a tape. The test builds the aeon of one read's lift micro-steps on `ClockLift` (one navigator
  of period 4) and reads its `epochs` at `ring_section(0, 4)`, which is the independent derivation of the
  reader's `crossing`.

[definition] Of the winding guide's six general objects the build touches the **helix** (the lift is
class plus carry, `ℤ/4` and not `ℤ/2 × ℤ/2`), **faces and placement** (the arrival is the placement of the
section crossing; the sub-tick position is the unresolved fibre), **cell holonomy** (the state carried
across the cells of the stream), **tube** (the port is the boundary of a longitudinal span, consumed as a
pairing on its clock `h`) and **continuation** (the stream is a section of the ring's state). The pair
stays attached through the arrival word and is not built: a lock of one ring against another is the pair
contact's, read from this owner's words by the owed lock reader. The tower thread is untouched.

## 4. Measured

[computational-witness; worker's run] `tests/acoustic_wave_port.rs`, run 4 of
[`native_runs.txt`](receipts/2026-10-09-acoustic-native/native_runs.txt): 8 passed, 0 failed, 0 ignored.
The first run (run 3) read 6 passed and 1 failed; §4.5 gives the failure.

### 4.1 The native step is the replica's, and every tick closes

The port's states `(u, w)` after `n` samples equal the replica's exactly at `n = 1, 2, 3, 7, 14`
(`u₁ = −288/145`, `w₁ = −576/145`; `u₂ = −82944/21025`, `w₂ = 1152/21025`; the denominators are `145ⁿ`, each
tick's solve dividing by the ring's `M = 145/32`), and the reflected waves at ticks 0–3 equal `b = −1017/145,
−148041/21025, −15608098/3048625, −2222771394/442050625`. The ring constants are the replica's
(`Y = 2`, `M = 145/32`, `K = 65/16`). At all 240 ticks `ReceivedTick::closes` holds and
`E′ − E = (hY/4)(a² − b²)` is recomputed in the test from the incident amplitude and the reflected wave
alone (`D = 0`); the quadrature coordinate stays zero and the remainders are zero. The stored energy at
tick 240 equals the sum of the booked boundary work, exactly, with no tape of states.

### 4.2 The state is the quotient

The same stream received in chunks of 1, 6, 113 and 120 samples gives, at each chunk boundary, the state of
the whole run at that tick, and all 240 tick receipts equal the whole run's. A reception drawn for 3 ticks
leaves the clock at 3; an empty wave consumes nothing. Refusals (typed): a wave of another admittance or
another step (`HnnError::Wave`), a driven coordinate outside the width, a nonpositive admittance or step,
and a pumped ring (`HnnError::Resonator`).

### 4.3 The dynamic section reads the replica's word and arrivals

Read from the settled state at tick 120, all 120 symbols `(class : advance)` equal the replica's 7-cycle
`1:+1 2:+1 3:+1 0:+1 1:+1 2:−2 0:+1` repeated, and the lift satisfies `ℓ_(k+1) = ℓ_k + Δℓ_k`, `ℓ mod 4 =
class`, `ℓ₁₂₀ = 1`, `ℓ₂₄₀ = 70`, with net lift 4 (one winding) per cycle. The section arrivals are at ticks
`122 + 7j`, `j = 0 … 16` (17 arrivals, all forward, gaps 7). `ℓ₂₄₀ = 70` reads as `17 + 1/2` turns
(`Reading`: windings 17, phase 1/2). The aeon owner reads the same arrivals independently: the micro-steps of
the lift on `ClockLift::new([4])` give an aeon ending at 70, `epochs` at `ring_section(0, 4)` has flux 17, is
monotone, and each tick falls in the sample and with the sign the reader named.

### 4.4 The arrival word is the observed placement

[computational-witness] The replica's bank gives, for the same wave, rings with the same cycle `τ = 7` and
different arrival words (series, never a sum; arrivals per sample over one cycle from tick 120):

| ring | cycle `(class : advance)` | `W` | arrivals per cycle | gaps | constant-rate (balanced) |
|---|---|---|---|---|---|
| `t = 1` | `1:+1 2:+1 3:+1 0:+1 1:+1 2:−2 0:+1` | 1 | `0 0 1 0 0 0 0` | 7, 7, … | yes |
| `t = 2` | `2:+1 3:+1 0:+2 2:+2 0:+1 1:−1 0:+2` | 2 | `0 1 0 1 0 0 0` | 2, 5, 2, 5, … | **no** |
| `t = 3` | `2:+1 3:+1 0:+2 2:+2 0:+1 1:−2 3:−1` | 1 | `0 1 0 1 0 −1 0` | 2, 2, 3, … | **no** |

Ring `t = 2` locks at the mean rate `W/τ = 2/7`, and a constant-rate word of rate `2/7` has gaps `⌊7/2⌋ = 3`
or `⌈7/2⌉ = 4` only (Lean `Aeon/Clock/CarryWord.carry_balanced`: the windows of one length differ by at
most one); its arrivals fall 2 and 5 apart. Ring `t = 3` closes one winding per cycle through three
crossings, one of them a departure back across the section. The native reader reproduces all three words
exactly (symbols over all 120 ticks; arrivals 121, 123, 128, 130, … for `t = 2`; `(121,+1) (123,+1)
(125,−1) (128,+1) (130,+1) (132,−1)` for `t = 3`). This is the reason the reader keeps the observed
arrival placement, the signed crossings, the lift and the residual (the sub-tick fibre), and keeps no rate:
a mean rate `W/τ` is a cycle face (`aeon::TwoClocks(W/τ)` would be one, beside the word, never in place of
it), and reading it as the arrival word is wrong on two of the three rings.

### 4.5 The polarity, and the failed first reading

The ring driven by `−x` has exactly the negative states at all 241 points, every symbol is
`(class + 2, Δℓ)` (the advance is invariant), and the lifts read from their own settled states differ by the
constant 2; the owner's `half_turn()` partner, started on `−z` at `ℓ + 2`, keeps the lift exactly 2 above and
reads the same advances.

[the failure, kept] The first run (run 3, 6 passed, 1 failed) failed this test at the assertion that the
signed crossing of the section is the same for `x` and `−x` (`left: 1, right: 0`). The assertion was
mine and it was wrong; the code was right. The half-turn is a symmetry of the **symbols**, and it carries
the section ray to the **opposite ray**: the arrivals of `−x` at the ray `ℓ ≡ 0` are the crossings of `x`
at the ray `ℓ ≡ 2`. The replica gives, for `−x` on the same ring `t = 1`, arrivals `(120,+1) (124,+1)
(125,−1) (127,+1) (131,+1) (132,−1) (134,+1) (138,+1) …`, 52 in the 120 ticks, three per cycle with a
departure, against the 17 single arrivals of `x`; the net flux is the difference of whole windings of the
endpoints, `⌊70/4⌋ − ⌊1/4⌋ = 17` for `x` and `⌊72/4⌋ − ⌊3/4⌋ = 18` for `−x`. The test now asserts the
opposite-ray law tick by tick and the replica's arrivals; the earlier assertion is not in the file, and its
failure is in `native_runs.txt`. The consequence for a design: the epochs of a passage at a ring's section
depend on the polarity of the wave unless the section is the half-turn-blind one (the sheet, both rays),
which cannot tell a half-wave antisymmetric tone from its half-shift (the second rung's X3).

## 5. The refusals that hold

[computational-witness] The origin (a ring at rest) has no class: `SectionReader::at(origin)` and the chord
from rest are refused `AtOrigin`, so a reader starts after the ring has left rest (the replica's settle
allowance, 120 samples, is its declared constant, not a result). A chord through the origin is refused
`ThroughOrigin`; a refused tick leaves the reader as it was. In the guard doctests (run 6) a `MatchedWave`
is never forged (`E0451`), is never made from an `Encoded` or turned into one (`E0277`, both ways), and each
type is refused where the other goes (`E0308`, both ways), with the error codes checked.

## 6. The strand question: what the build adds, and one measurement

[open; a limitation, reported] The second rung's §6 asked whether a ring's readings form a strand (words on a
navigator's helix with residues, whole windings and epoch readings; a letter chart; a pairing the pair
contact reads). What this build adds: the ordered `(class, advance, crossing)` stream and the lift now exist
natively on the exact tick clock, as residues of a declared ring of period 4 with carry, and the half-turn
is a fixed-point-free involution on the classes with the advance fixed (`cls → cls + 2`), the dyad's `U`. The
stream is read and dropped; nothing stores it, so the strand as a retained object would be the phase-carried
moment, not a tape of symbols, and it is not built. No letter chart, no face and no contact exist.

[measured; the second rung's own falsifier] The second rung wrote: "falsifier: a ring whose symbol word is
not a located route on its `ℤ/4` helix under `LocatedTransport`". The test measures it. On ring `t = 1` the
advance is **not a function of the class**: class 2 advances by `+1` at one place of the cycle and by `−2`
at another (asserted), so the word is not a located route on the ring's own `ℤ/4` helix, whose advance
depends on the emitted class alone. The hidden state is the ring's own `(u, w)` inside the quadrant.

[measured, predicted by the first rung's replica before the Rust ran] The first rung's frame family
(`FrameFamily::pairs(6)`) reads the native symbol word of ring `t = 1` (5 distinct symbols over period 7,
`0 1 2 3 0 4 3` by first occurrence, three cycles) as `FrameTally { narrow: 7, empty: 0, plural: 5, open: 0,
one: 0 }`: no frame carries it, and the period is held. The replica's prediction
([`symbol_word_prediction_output.txt`](receipts/2026-10-09-acoustic-native/symbol_word_prediction_output.txt))
gives the same tally, with 12, 108, 462, 5424 and 3228 gauge classes on the five frames wide enough; its
bound-9 scan did not finish in its 300 s deadline and is incomplete, not relaunched. The word was not chosen
to fail: it is the settled word of the replica's ring `t = 1`. It says the symbols of a single ring are not an
orbit of a first-rung navigator, so the owed join of the second rung's §6 (a located transport per ring over
`(class, advance)`) cannot be the first rung's frames as they are.

## 7. Recorded failures checked

- **An authored routine standing in for learning** (failure 1, lesson 5; guard 17). The risk remains and is
  not removed: a declared quadrant classifier on a declared ring, read at its sign crossings, is a
  Goertzel-like analyzer. What it claims is the **wave receiver and the section reader**, not learning: the
  reader sees the ring's own state, no candidate period or rate is enumerated, and nothing is located. The
  four rays are a declared grain with its reason (§3); the ring is the replica's declared one.
- **Text, or a sample, run as the exception** (failure 3, lesson 2). `MatchedWave` carries exact amplitudes
  at a declared port, and `SectionReader` takes any plane point; nothing in either is acoustic. The
  calibration of a recording is the boundary chart's.
- **A fixture as the goal** (lesson 12). The fixture is the replica's F1 and its bank's rings `t = 1, 2, 3`,
  with the replica's settle allowance; none was tuned. The words of `t = 2, 3` were chosen to be read
  because the replica showed them unbalanced, which is what the test is about, and are disclosed as such.
  A pass on one period-7 wave on three rings is not a claim about sound.
- **A sum replaced its series** (failure 18, lesson 19). Every reading is a series: symbols, arrivals with
  signs, gaps, arrival words per cycle; `W/τ` is named a face beside them.
- **A mean rate read as the actual arrival word** (Codex's boundary): §4.4.
- **A located cause carried unrepaired** (lesson 3). The plural fibres of the first rung are the located
  cause of §6's tally and stay open in their owner.
- **Programming words for the physics** (failure 19). The design is stated in rays, classes, windings,
  section crossings and the port's power; the iterator, the chunking and the receipts are the realization.

## 8. Not claimed

- That the bank, the quarter-turn grain or the ring is learned or located; that any real recording, noise,
  polyphony or drifting pitch reads; that anything decodes to sound or anything generative or perceptual is
  measured.
- That a lock is read: no least period of the settled word, no `W` from the net lift, no `aeon::TwoClocks`
  face, no near-return grain was built. The words above are read by eye and by the test's explicit cycles.
- **That the state is bounded.** The exact state's denominators grow by the factor `145` per tick at `t = 1`
  (the printed states: `145, 145², 145³, …, 145¹⁴`), so the carried state's bits grow linearly with the
  ticks. It is the exact law without a lattice; the lattice carry with remainders (`hnn::chart`) is the owed
  bounded realization, and `WavePort` refuses a lattice ring today.
- Pumped rings, nonlinear rings, a second driven coordinate, a stereo wave; any join to `hnn::word`,
  `Resident` or deposition (the mode state is word-local in `Word` and is dropped at its end; `WavePort` is
  outside any word and is not mounted); any change to `world_boundary`.
- That a chord is the right interpolation for a ring that turns half a turn or more per tick (it aliases and
  is not detected; an exact half turn is refused). The bank's rings turn less.
- That the strand is contactable (§6), or that writing is received as oriented packing through foveation.
- Lean: nothing new is kernel-checked; the obligations are in §10.

## 9. What remains

**The lock reader (item 4).** The reader that turns a settled word into a lock: the least `τ` for which the
`(class, advance)` word is exactly `τ`-periodic (the first-return test, on the exact word), `W = (Σ_(k<τ) Δℓ_k)/4`
(a closed class cycle has a whole winding; the net lift is `4W`), the address `W/τ` in lowest terms, and
`aeon::TwoClocks::new(W/τ)` with `lock_address`, `convergents` and `near_return` as a **mean-rate face
beside the observed arrival word** (§4.4), the near-return grain where no exact lock exists. What this build
gives it: the symbol stream with the lift and the signed crossings, exact, per tick. What it lacks: the
periodicity test, `W`, the `TwoClocks` construction and the refusals (`Unlocked`, `Silent`).

**The strand.** A located transport per ring over `(class, advance)` with the hidden state the ring carries
(§6: the first rung's frames hold it), a letter chart, and a contact whose rate port reads the ring's `W/τ`
or its convergent and whose placement port reads the arrival word.

**Also owed from the second rung:** the joint period (the lcm of the rings' least periods), the amplitude
receipt `Ē_b(x) = xᵀQ_bx`, the gauge `decode(σ(encode x)) = x` into the wave port, the render
`g·Σ_b b_out = q + r`, the pumped port, and the bounded (lattice) realization of the carried state.

## 10. Obligations owed to #62

Lean statements not yet stated (the hand derivations are `proved-derived`):
1. The unpumped tick under a matched source: the port balance with the wave booked as boundary work (the
   existing `ring_tick_executed_energy_balance` with the incident less the reflected energy) and the chunk
   law `s_((j+1)g) = Tᵍ s_(jg) + Σ_a T^(g−1−a) B x_(jg+a)` (the carried state is the quotient).
2. The chord's advance: for `p × q > 0` the class advance `(cls q − cls p) mod 4` lies in `{0, 1, 2}`, its
   negative counterpart, `Δℓ(−p, −q) = Δℓ(p, q)` and `cls(−z) = cls z + 2`.
3. The crossing is the flux: `⌊(ℓ + Δℓ)/4⌋ − ⌊ℓ/4⌋` is the signed count of `ring_section(0, 4)` over the
   lift's micro-steps (the instance of `signed_count_is_flux`), and the opposite-ray law of §4.5.
4. The arrival word of a ring under a periodic wave is eventually periodic, and is **not** in general the
   carry word of its cycle rate: the counterexample of §4.4 (`t = 2`: `W = 2`, `τ = 7`, arrivals `0101000`).
5. The advance of the symbol word depends on more than the class (§6): the ring's symbol word is not an orbit
   of `ℤ/4` under a class-determined advance.

## 11. Owners

New: `hnn::wave::{MatchedWave, WavePort, Receiving, ReceivedTick}`;
`hnn::dynamic_section::{SectionReader, SectionSymbol, SectionRefusal, quadrant, chord}`; `HnnError::Wave`;
`tests/acoustic_wave_port.rs`; atlas rows `hnn.matched-wave-port`, `hnn.dynamic-section-lift`,
`wave.arrival-word-is-not-the-mean-rate`. Consumed unchanged: `hnn::ring::{ResonatorMaterial,
ResonatorOperands::step, ResonatorStep::closes}`, `aeon::{Reading, ClockLift, epochs}`,
`compression::keys::frames::FrameFamily` (the probe). Changed: THE_MACHINE guard 9 gains the bullet "a wave
is not a code". Receipts: [`receipts/2026-10-09-acoustic-native/`](receipts/2026-10-09-acoustic-native/).
