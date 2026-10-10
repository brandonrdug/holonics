# A matched wave enters a loaded ring, and its state crosses its own section

**Date.** October 9. **Issues.** #148, #73, #386, #62. **Grade.** Native build of items 1–3 of the
second rung's native list (§§1–11) and of its items 4 and 5, the lock reader and the joint period (§12),
against numbers read from an independent exact replica. Each claim carries
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
- Reason for the narrow admission (corrected in §13): the consumer equation is the unpumped exact one, and the port is the passive one (`K ⪰ 0`). A pumped, scheduled,
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
- That a lock was read in §§1–11: the words there are read by eye and by the tests' explicit cycles. The lock
  reader and the joint period are §12's; the near-return grain (`TwoClocks::near_return`, for a stretch that
  is only near-periodic) is not built.
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

**The lock reader (item 4)** and **the joint period (item 5)** are built, as consumers of the dynamic
section's stream (§12). What remains of them: the near-return grain for a stretch that is only
near-periodic (no exact lock), and the amplitude and placement ports of the contact that would read two
rings' addresses against each other.

**The strand.** A located transport per ring over `(class, advance)` with the hidden state the ring carries
(§6: the first rung's frames hold it), a letter chart, and a contact whose rate port reads the ring's `W/τ`
or its convergent and whose placement port reads the arrival word.

**Also owed from the second rung:** the amplitude receipt `Ē_b(x) = xᵀQ_bx`, the gauge `decode(σ(encode x)) = x` into the wave port, the render
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
`hnn::section_lock::{LockWindow, LockReader, Settled, Lock, Arrival, LockRefusal, JointLock, JointRefusal}`;
`tests/acoustic_wave_port.rs`; atlas rows `hnn.matched-wave-port`, `hnn.dynamic-section-lift`,
`hnn.section-lock`, `hnn.joint-period`, `wave.arrival-word-is-not-the-mean-rate`. Consumed unchanged: `hnn::ring::{ResonatorMaterial,
ResonatorOperands::step, ResonatorStep::closes}`, `aeon::{Reading, ClockLift, epochs}`,
`compression::keys::frames::FrameFamily` (the probe), `aeon::TwoClocks` and `navigator::address::LockAddress`
(the mean-rate face). Changed: THE_MACHINE guard 9 gains the bullet "a wave
is not a code". Receipts: [`receipts/2026-10-09-acoustic-native/`](receipts/2026-10-09-acoustic-native/).

## 12. The lock reader and the joint period

[project-postulate] The coordinator's third task: the second rung's items 4 and 5, as a **consumer** of
`SectionReader`'s stream, in [`section_lock.rs`](../../crates/holonics/src/hnn/section_lock.rs). No render, no
strand contact and no learning.

### 12.1 The acceptance, fixed before the Rust ran

The reading was specified and predicted in
[`lock_predictions.py`](receipts/2026-10-09-acoustic-native/lock_predictions.py), which loads the
acoustic-locks replica `6d96dfcc…` and applies the reading to its settled symbols; its output
([`lock_predictions_output.txt`](receipts/2026-10-09-acoustic-native/lock_predictions_output.txt)) was written
before the lock tests were run. The window is the replica's: settle tick 120, 120 ticks read. The declared
bank is three rings of the replica's Farey bank, `t = 2/3, 1, 2` (`κ = 1/8`, so `a = t/8`), never searched or
tuned. The reading, exact equality of symbols, no tolerance:

```text
τ        the least τ ≤ 60 (half the window) with s_k = s_(k+τ) for every k < 120 − τ      else Unlocked
W        (Σ_(k<τ) Δℓ_k)/4, whole turns (Fractional, retired in §14: the admitted word turns whole)
address  W/τ in lowest terms;  arrival word = the signed crossings of one cycle, as observed
Silent   no symbol of the window advances the lift
joint    the lcm of the locked rings' τ, silent rings skipped, any other refusal refuses it;
         it equals the least period of the tuple word and divides the wave's period
```

### 12.2 Owners and the missing term

| Step | Existing owner | Missing term | Built |
|---|---|---|---|
| The ring's symbols | `hnn::dynamic_section::SectionReader` (this record, §3) | Nothing reads a word across ticks | consumed |
| The cycle and its winding | `aeon::Reading` (windings plus phase), `Geometry/PhaseCarry.closed_loop_has_integer_winding` | The least period of the settled word, `W` from the net lift, the typed refusals | `Settled::lock`, `Lock`, `LockRefusal` |
| The address as a face | `aeon::TwoClocks::{new, lock_address, convergents}`, `navigator::address::LockAddress` | Constructed from a given ratio; never from an observed cycle | `Lock::mean_rate_face`, beside the word |
| The ring at rest | `SectionReader::at` refuses the origin | A ring that never leaves rest has no stream | `LockReader` reads it as `Settled::Rest` |
| The joint period | none | The lcm of the rings' cycles and its identity with the tuple word's period | `JointLock` |

### 12.3 Choices and their reasons

[definition; agent-inferred]
- **The Unlocked bound is half the window** (the brief): a period of at most 60 ticks is a period the 120-tick
  window shows at least twice. The replica reads at most a third (40, three repetitions); the rings' cycles
  here are 4, 7 and 12, so the readings coincide, and the prediction was run at 60.
- **Silent is "no symbol advances the lift"**, not "no section arrival". The replica's own F3 reading is the
  reason: ring `t = 2` on F3 rocks across the ray 2 without ever arriving at the section and locks at `τ = 12`
  with `W = 0` (the replica's "lock without rotation"). Read literally, "no section arrival" would call it
  Silent and lose its cycle. It is a lock with an empty arrival word and no mean-rate face. A ring at rest
  (the origin has no class) is never started: it is Silent by being at rest (zero input).
- **Fractional was typed and unreachable from a reader's stream** (superseded in §14). The reader's symbols
  satisfy `class_(k+1) = class_k + Δℓ_k (mod 4)`, so a word that repeats in the class has a net lift
  `≡ 0 (mod 4)`. The refusal was the typed form of the replica's assertion L9 for hand-fed symbols that break
  the recursion. It did not check the crossings, and §14 replaces it with the admission of the word.
- **The read window is the declared finite read set**, held at most 120 symbols and dropped with the reading;
  it is not retention of the stream. `LockReader::observe` is atomic, ignores ticks before the settle tick and
  after the window, refuses a ring that was at rest at the settle tick and leaves rest inside the window
  (`NotSettled`), and refuses an unfilled window (`Incomplete`).
- **The face exists only for `W > 0`** (`TwoClocks` needs a positive rate) and sits beside the word.
- **The joint period is the lcm, each ring's `τ` divides it, and it divides the wave's period.** The brief
  says the joint "must divide every ring's own observed period"; that cannot hold, and the replica's F4 shows
  it: rings read `τ = 4` and `τ = 12`, the joint is 12, and 12 does not divide 4. The law that holds, and
  that is asserted, is the converse: every ring's cycle divides the joint, and the joint divides the wave's
  period (7 for F1, 12 for F3 and F4). The joint reading also checks that the least period of the tuple of the
  rings' symbols is the lcm (`JointRefusal::Disagrees`): by Fine–Wilf, a window of length `τ_b + p` carrying
  periods `τ_b` and `p` carries their gcd, so with the lcm at most half the window the tuple's least period
  `p ≤ lcm` is divisible by every `τ_b`, hence is the lcm. An lcm over half the window is refused
  (`Beyond`): the window would not show it twice.

### 12.4 Measured

[computational-witness; worker's run] `tests/acoustic_wave_port.rs`, 13 passed (the 8 of §4 and 5 new), plus 8
unit tests of `hnn::section_lock`; every value equals `lock_predictions_output.txt`, and the cycles, windings
and addresses equal the replica's own `run_output.txt` at `35d59516` (F1 `W = 1, 1, 2`; F3 `τ = 12`, `W = 1,
1, 0`; F4 `τ = 4, 12, 12`, `W = 1, 3, 3`, address `1/4`). Arrivals as (tick : sign), series per ring:

| wave (period) | ring | `τ` | `W` | address | arrival word over a cycle from tick 120 | arrivals |
|---|---|---|---|---|---|---|
| F1 sawtooth (7) | `2/3` | 7 | 1 | `1/7` | `0 0 1 0 0 0 0` | 122 |
| | `1` | 7 | 1 | `1/7` | `0 0 1 0 0 0 0` | 122 |
| | `2` | 7 | 2 | `2/7` | `0 1 0 1 0 0 0` | 121, 123 |
| F3 quantized triangle (12) | `2/3` | 12 | 1 | `1/12` | arrival at offset 3 | 123 |
| | `1` | 12 | 1 | `1/12` | arrival at offset 2 | 122 |
| | `2` | 12 | 0 | `0` | `0` × 12 | none |
| F4 two-tone 3 + 4 (12) | `2/3` | 4 | 1 | `1/4` | `0 0 0 1` | 123 |
| | `1` | 12 | 3 | `1/4` | `0 0 1 0 0 0 1 0 0 0 0 1` | 122, 126, 131 |
| | `2` | 12 | 3 | `1/4` | `0 1 0 0 0 1 0 0 0 0 1 0` | 121, 125, 130 |

- **Joint periods:** F1 7 (divides 7), F3 12 (divides 12), F4 12 (lcm of 4, 12, 12; divides 12; every ring's `τ`
  divides it), each equal to the least period of the tuple word (checked by the joint reading).
- **The face is beside the word, and is not it.** On F1 each ring's `TwoClocks(W/τ)` has lock address of
  period 7 and its last convergent is the address; the word of ring `t = 2` is not balanced (§4.4) while the
  two others' are. On F4 ring `t = 1` has the face `1/4` with lock period 4 on a cycle of 12: the face
  does not read the cycle.
- **Refusals, as measured:** Thue–Morse (replica fixture F5) is `Unlocked { max_period: 60, length: 120 }` on
  all three rings and refuses the joint at ring 0; the sawtooth of period 61 (one over half the window) is
  Unlocked on all three; zero input is `Silent` on all three and for the joint; a wave that starts at tick 130
  leaves a ring at rest at the settle tick and is refused `NotSettled`; a reader offered 201 of the 241 states
  is refused `Incomplete`. Unit tests (explicit symbol words): `Silent` for no ray crossed, the 13-cycle
  `Unlocked` and the 12-cycle locked at exactly half the window, `Fractional { period: 1, net: 2 }` (retired in §14), the
  rocking lock with `W = 0`, the departure `−1` in an arrival word, and the joint (4 and 6 give 12; a silent
  ring skipped; all silent `Silent`; an unlocked ring refuses it; 4, 6 and 5 give 60 `Beyond`).

### 12.5 Recorded failures checked

- **An authored routine standing in for learning** (failure 1, lesson 5; guard 17). This is a least-period
  test on an exact word against candidate periods `τ ≤ 60`: it enumerates candidates, so the risk is real. What
  it reads are the ring's own section symbols, not samples; the bank is declared and not searched; and the
  claim is the reader, not learning.
- **A mean rate read as the actual arrival word** (Codex's boundary). The lock's content is the cycle and the
  observed arrival word; `TwoClocks(W/τ)` is `mean_rate_face()`, beside it, only for `W > 0`.
- **A sum replaced its series** (lesson 19). Per ring `(τ, W, address)` and the signed arrival word, never a
  joint score; the joint period is stated with its rings' periods.
- **A fixture as the goal** (lesson 12). The tones are the replica's F1, F3, F4 and its controls; the three
  rings were fixed before the run; ring `t = 2` was chosen because the replica shows it unbalanced on F1 and
  rocking on F3 (disclosed), and the other readings were predicted, not tuned.

### 12.6 Not claimed

That a lock is learned or located; that a near-periodic stretch locks (no `near_return` grain); that the joint
over many rings stays within a window (the lcm over half the window is refused); that any real recording
locks; that the address pairs two rings (no contact is built). The runs are a worker's, not the validation
queue's; clippy and the guard lints were not run.

### 12.7 Obligations owed to #62

6. The least period of a settled symbol word and its winding: a closed class cycle has a whole winding
   (`closed_loop_has_integer_winding` for the reader's class recursion), and the face `TwoClocks(W/τ)` has the
   lock period of `W/τ` in lowest terms, which divides the cycle's `τ`.
7. The joint period: for words with periods `τ_b` on a window of length at least `2 lcm`, the tuple's least
   period is the lcm (Fine–Wilf), and it divides the wave's period when the wave's steady state has that period
   (the second rung's L7, L8).

## 13. Codex's source review: two defects repaired, and stated limits

[source-inspected; Codex, review of §§1–11] Two concrete defects in `hnn::wave`, both exact witnesses. Both
are repaired and pinned by tests (`a_signed_stiffness_is_not_a_passive_port`,
`every_coordinate_of_the_port_reflects`; 15 passed in `tests/acoustic_wave_port.rs`).

**1. Passive admission.** `ResonatorMaterial::new` enforces `C ⪰ 0` and `D ⪰ 0` and only the symmetry of `K`; the
loaded-solve certificate `2C + hD + (h²/2)K ⪰ 0` makes the operator solvable but does not make the storage
positive. `WavePort::at_rest` therefore admitted a non-passive ring. The witness is `C = I`, `K = −I`,
`D = 0`, `h = Y = 1`, incident amplitudes `1` then `0` on one coordinate (the test runs the owner's own steps):

| tick | `u` | `w` | `b` | `E = ½(w C w + u K u)` | balance |
|---|---|---|---|---|---|
| 1 | `2/5` | `4/5` | `1/5` | `6/25` | closes |
| 2 | `6/5` | `4/5` | `−8/5` | `−2/5` | closes |

The incident energy totals `1/4` and the reflected `1/100 + 64/100 = 13/20`: the ring was repaid more than it was
given, with both balances closed and a negative stored energy. The repair: `WavePort::at_rest` requires
`K ⪰ 0`, decided exactly by the inertia owner (`ratio::linear::inertia`, no negative direction), and refuses a
signed `K` with `HnnError::Resonator`. `C ⪰ 0` and `D ⪰ 0` are already the owner's, and positive definiteness of
`C` is not needed: `E ≥ 0` needs only semidefiniteness, and the port's own `(h/Y) I` keeps the solve definite.
With `E ≥ 0`, the balance gives `Σ boundary_work ≥ E ≥ 0` from rest, so the port cannot be repaid more than it
brought. A free mass (`K = 0`) and a coupled positive `K` are admitted (asserted). A signed stiffness is a boost
and keeps its own owner (the signature path); this port is the passive one.

**2. The return contract.** `reflected_energy` summed every output, but `ReceivedTick.reflected` carried only the
driven coordinate, so a consumer recomputing the work from the incident amplitude and that one entry booked the
wrong quantity when `K` couples the coordinates. The witness is `C = I`, `K = [[2, 1], [1, 2]]` (positive
definite), `h = Y = 1`, input `(1, 0)`: `ω = (16/63, −2/63)`, reflected `b = (31/63, 4/63)`, and the work booked
over the full port vector is `(hY/4)(|a|² − |b|²) = 748/3969`, where the driven coordinate alone gives
`752/3969`. The repair: `ReceivedTick.reflected` is now the whole reflected vector (with `coordinate` and the
accessor `driven_reflected()`), `closes()` also requires it to be the owner's output, and the module header
states that the boundary work is over the full port vector. The test asserts the vector, `748/3969`, that it
differs from `752/3969`, the incident and reflected energies, and that the stored energy from rest is `748/3969`.

[computational-witness; worker's run] The first run after the repair passed all 15 tests; `native_runs.txt`
(runs 12 to 15) has the commands. The existing first test now also asserts the isotropic node's quadrature
coordinate reflects nothing.

**Stated limits** (Codex's other boundaries; everything built here is narrower than they say):
- The quarter-turn grain is not continuous phase. A class is a quadrant at a declared grain; the lift keeps the
  class and the whole winding, and the phase inside a quadrant (the exact angle of the state) is neither carried
  nor read. Two states of one class differ in phase unresolved.
- `SectionSymbol` carries no receiver, no clock and no subtick placement. It is `(class, advance, crossing)` of
  one declared section; whose section it is (a receiver's frame), the clock it is read on (the port's `h`, the
  tick index belongs to the caller) and where inside the tick a crossing falls (the unresolved fibre below the
  tick) are not in it.
- Chunk invariance does not certify gaps. §4.2 shows that receiving a stream in chunks with the state carried
  equals receiving it whole; a stream with a stretch missing (dropped samples, a gap in the clock) is a different
  wave, and the port has no notion of one: nothing checks the continuity of the clock between chunks beyond its
  own tick count.
- A declared quadrant grain is not a founded symbol identity. The symbols are labels of a declared partition of
  the plane; they are not classes of a founded encoding, not located, and not shown invariant under relabelling,
  so two rings reading equal labels have not thereby read the same symbol. (§6: the first rung's frames hold the
  word.)

## 14. The second review: a forged word was admitted, and the word now carries its certificate

[source-inspected; Codex, independent review of `aeeb0ee8`] Both §13 repairs hold. The review found one more
defect: `Settled::Word(Vec<SectionSymbol>)` was publicly constructible, and `Settled::lock` read its symbols
without checking that they were a section's. The witness, in a four-tick window, repeats
`(class, advance, crossing) = (0, 2, 0), (2, 2, 0)`. The class recursion closes and the net lift is `4`, so the old
reading admitted a lock of period `2` and winding `1` with the arrival word `[0, 0]`. The second tick lands on
`2 + 2 = 4` and must cross `+1`. The lock reader trusted content that only the reader's own stream guaranteed.

[definition; agent-inferred] **The repair is private construction.** `Settled::Word` now holds a `SectionWord`,
whose symbols are private and which is admitted only by `SectionWord::new` (or built by the `LockReader` from the
ring's own states). The admission checks four chart relations at every tick and refuses
`LockRefusal::NotASectionWord { tick, relation }` at the first broken one:
- `class ∈ {0, 1, 2, 3}`;
- `Δℓ ∈ {−2, …, 2}` (a chord turns less than half a turn: `dynamic_section::chord`);
- `crossing = ⌊(class + Δℓ)/4⌋`;
- the class recursion `class_(k+1) = class_k + Δℓ_k (mod 4)`.

The reason for private construction over validating inside `lock`: the joint reading and any later consumer of a
word read the same symbols, and a certificate in the type reaches them all.

[proved-derived] **The winding is the signed count of the arrivals.** Summing
`class_(k+1) = class_k + Δℓ_k − 4·crossing_k` over a cycle of an admitted word of period `τ ≤ L/2` (so
`class_τ = class_0`) gives `Σ Δℓ_k = 4 Σ crossing_k`, so `W = Σ_(k<τ) crossing_k`. `Fractional` became
unreachable for every admitted word and is retired; its old hand-fed case `(0, 2, 0)` repeated is now refused at
tick `0` (`Recursion`). `Settled::lock` keeps the two identities as debug assertions.

**Zero winding does not empty the arrival word.** The atlas row `hnn.section-lock` said that a lock of winding `0`
has an empty arrival word. That holds for F3's ring `t = 2`, which rocks across the ray 2 and never reaches the
section, and it is not a law: `(3, +1, +1), (0, −1, −1)` returns to class 3 with net lift `0` and arrives and
departs, `[+1, −1]`. The row, the module header and the rocking test's name now keep the two apart.

Tests (unit, `hnn::section_lock`):
- `a_word_that_breaks_a_chart_relation_is_not_admitted`: the review's witness is refused at tick `1`
  (`Crossing`), and the same word with the crossing it owes locks at `τ = 2`, `W = 1`, arrivals `[0, 1]`. The
  half-turn word is refused (`Recursion`), as are a class `4` (`Class`) and an advance `3` (`Advance`). A reader's
  own stream around the circle is admitted.
- `a_lock_without_rotation_can_arrive_and_depart`: the zero-winding witness locks at `τ = 2`, `W = 0`, arrivals
  `[+1, −1]` at ticks 10 and 11, no face.
- `the_signed_arrivals_of_a_cycle_sum_to_its_winding`: four cycles, including the record's rings `t = 1, 2, 3`
  and a negative winding.
- `a_rocking_lock_that_never_reaches_the_section_has_an_empty_arrival_word` (renamed from
  `a_lock_without_rotation_is_a_lock_with_an_empty_arrival_word`; its assertions are unchanged).

The admission also refused one of the original fixtures. The joint test's unlocked ring,
`(k mod 4, 1 − ⌊k/12⌋)`, steps from class `0` to class `1` with no advance at tick 13: a forged word that had
stood in for an unlocked one. It is now a section word with the same role: twelve quarter-turns, then rest at
class 0, which no period of at most 12 repeats. The ring still refuses the joint (`Ring { ring: 1 }`). The other
unit tests and the integration tests are unchanged, and they build words through `SectionWord::new` or the
reader. The finite window stays a hypothesis: a lock is a repetition inside the declared window, not a proof that
the steady state is periodic beyond it.

## 15. The section owners call the winding owners at their consumers

[project-postulate] #386, #148. The coordinator's brief called this subsection §14; §14 is the second review above, so
the join is §15. The survey that opened it found the section owners restating a law their neighbours already own:
`section_lock::Settled::lock` divided the cycle's net lift by four and asserted the result, `SectionWord::new` compared
`class + Δℓ` with four by hand, and `SectionReader::advance` compared it with `0` and `4`, while
`geometry::winding::closed_loop_winding` had no consumer outside its tests and `aeon::Reading::add` (the signed carry
law, over `geometry::winding::carry`) none outside its own. This section replaces each hand computation by the call to
the owner at the consumer and proves equality with the old reading on the declared bank. The recorded failure it could
repeat is "a search hit is not a join" (lessons, September 29 and October 9): a docstring naming an owner joined
nothing, so each row below is a call and a test.

### 15.1 The equations now stated at each consumer

| Consumer | Equation | Owner called |
|---|---|---|
| `dynamic_section::land`, called by `SectionReader::advance` and `SectionWord::new` | `crossing = windings(Δℓ/4) + carry(cls/4, Δℓ/4) = ⌊(ℓ + Δℓ)/4⌋ − ⌊ℓ/4⌋ ∈ {−1, 0, 1}`; `cls′ = 4·openPhase(ℓ/4 + Δℓ/4)`; the carry depends on `ℓ mod 4`, not the winding | `aeon::Reading::{of_turns, add}`, which calls `geometry::winding::carry` (Lean `Aeon/Clock/Winding.windings_add`, `carry_le_one`) |
| `section_lock::cycle_winding`, called by `Settled::lock` | `W = closed_loop_winding(4, (Δℓ_k)_(k<τ))`: the advances close on four rays, else refused with the exact remainder | `geometry::winding::closed_loop_winding` (Lean `Geometry/PhaseCarry.closed_loop_has_integer_winding`) |
| `SectionWord::winding` | `W(u) = windings(c_u/4 + N_u/4) = ⌊(c_u + N_u)/4⌋`, `N_u = Σ Δℓ_k`, the carry law applied once to the start class and net lift | `aeon::Reading::add` |
| `SectionWord::concat` | `e(u) = c_v ⇒ W(uv) = W(u) + W(v)`; `e(u) ≠ c_v ⇒ NotASectionWord { tick: |u| − 1, Recursion }`, no winding | the cocycle `windings_add`, `carry_cocycle`, `aeon_windings_concat` |

The concatenation derivation: with `e(u) = (c_u + N_u) mod 4`, `⌊(e(u) + N_v)/4⌋ = ⌊(c_u + N_u + N_v)/4⌋ −
⌊(c_u + N_u)/4⌋`, so the junction carry is zero exactly when the junction phase is the class both words agree on.

### 15.2 Choices and their reasons

[definition; agent-inferred]
- **One statement of the tick's law.** `land(class, advance) -> (crossing, landed class)` is the only place that
  carries a quarter-turn tick. The reader emits its symbol from it and `SectionWord::new` admits a symbol against it,
  so the chart relation `crossing = ⌊(class + Δℓ)/4⌋` and the class recursion cannot drift from the reader. The lift
  itself still adds `Δℓ` as an integer, which is no carry. `LockReader::finish` now admits the reader's symbols through
  `SectionWord::new` instead of trusting the comment that they satisfy the relations.
- **The lock's winding is the closed-loop owner's.** Its refusal (`LockRefusal::Winding`) replaces the two
  `debug_assert`s: a loop that does not close is a typed return carrying `LoopDoesNotClose { modulus, remainder }`, in
  release builds too. For an admitted word it is unreachable (the least period `τ ≤ L/2` makes the class repeat, and the
  recursion then closes the lifted sum), and it is tested directly on non-closing cycles (`cycle_winding`).
- **The conversion is lossless, and refused if not.** The owner returns a `BigInt`; the lock keeps `i64`. `|Σ Δℓ| ≤ 2τ`
  and `τ ≤ L/2` give `|W| ≤ L/4`, below `i64::MAX` on any platform whose `usize` is at most 64 bits.
  `LockRefusal::WindingBeyondCarrier { winding }` returns the exact integer rather than narrow it, and
  `SectionRefusal::Carrier` does the same for `land`'s `i8` and `u8` (the crossing is at most one more than the quarter
  turns of `Δℓ`, `carry_le_one`). Both are unreachable and typed. `SectionWord::winding` returns a `BigInt` and needs no
  narrowing.
- **`SectionWord::winding` does not sum the `crossing` fields.** It is the carry law applied once to the word, so that
  `W(uv) = W(u) + W(v)` is a statement about the owner's cocycle and not a tautology of a sum. That `W` equals the signed
  count of the arrivals (the telescoped per-tick law the old `debug_assert` stated) is asserted instead, on every
  declared lock and on every cut of every bank ring.
- **The `i8` chord and the half-turn partner stay as they were.** `chord` (the advance) and `SectionReader::half_turn`
  (`ℓ + 2`, the class `+ 2`) are the chart's own definitions with the Lean owed in §10 item 2; they are not a
  carry and were not joined.

### 15.3 Measured

[computational-witness; worker's run] Every existing test passes with its asserted values unchanged (no assertion was
edited): `tests/acoustic_wave_port.rs`, 17 passed (the 15 of §13 and two new), and the unit tests of the four modules,
39 passed (`hnn::section_lock` 12, `hnn::dynamic_section` 9, `geometry::winding` 10, `aeon::reading` 8). The new tests:
- `dynamic_section::tests::the_landing_is_the_owners_signed_carry_law`: `land` equals the hand law, kept in the test only
  as an independent oracle, on every `i8` advance from the classes `0, 1, 2, 3, 4, 7, 255`, and the six boundary
  landings (`land(3, +1) = (+1, 0)`, `land(0, −1) = (−1, 3)`, …).
- `…the_crossing_is_the_difference_of_the_lifts_whole_windings_at_every_winding`: for lifts `ℓ = −9 … 9` and `Δℓ ∈
  {−2, …, 2}` the crossing is the difference of the windings of `Reading::of_turns(ℓ/4)` and of `(ℓ + Δℓ)/4`, and the
  landing class is the open phase times four: the carry is a function of the phase alone.
- `…the_reader_emits_the_landing_at_every_tick_and_its_reading_keeps_the_windings`: along a walk with two arrivals and
  a departure, each tick's symbol is `land`'s, `reading().windings()` moves by the crossing, and the lift ends at `4`.
- `section_lock::tests::a_cycles_winding_is_the_owners_and_an_open_cycle_is_refused_with_its_remainder`: windings `1,
  −1, 2, 0` for closed advance cycles; the sums `1, 3, −1` are refused `LoopDoesNotClose` with remainders `1, 3, −1`.
- `section_lock::tests::words_concatenate_with_the_carry_cocycle_when_their_classes_meet`: `W = 0, 1` for two words
  joining to `1`; a departure `−1` meets its return `+1` at `0`; a word on another class is refused `Recursion` at
  tick `1`; the empty word is the identity.
- `tests/acoustic_wave_port.rs::section_words_concatenate_with_the_carry_cocycle_on_the_declared_bank`: the three ring
  words of the declared bank on F1 (`t = 2/3, 1, 2`, 120 symbols each), cut at ten declared ticks. A word equals the join
  of its parts at every cut with `W` additive, and is associative over three parts. Every cut of every ring joined to
  every cut of every ring: where the landing class of `u` is the start class of `v` the join exists, `W(uv) = W(u) +
  W(v)` and equals the signed arrival count; everywhere else it is refused `Recursion` at `u`'s last tick; both outcomes
  occur.
- `…::a_locks_winding_is_the_closed_loop_owners_the_words_and_the_arrivals`: on all nine locks of the bank (F1, F3, F4)
  the lock's `W` (closed-loop owner) equals the winding of its cycle as a section word (carry law) and the signed sum
  of its arrival word, and the cycle lands on the class it starts from.

Runs, under the common lease, `CARGO_BUILD_JOBS=4`, test threads 4, scratch in the worktree's `.local/`:

| Run | Projection and deadline | Result |
|---|---|---|
| `cargo test -p holonics --test acoustic_wave_port` | at most 420 s (the largest earlier unit was 70 s) | exit 0, 17 passed; the build took 21 s and the tests 19 s; the 717 s of wall time in its BOUNDED line include about 670 s waiting for the lease |
| `cargo test -p holonics --lib -- hnn::section_lock hnn::dynamic_section geometry::winding aeon::reading` | 420 s | exit 0, 39 passed, 36 s wall (build included) |
| `bash tools/gate.sh`, first run | 420 s | exit 1 in 50 s: `check` ok, `guard-doctests` ok (63 passed), `guard-lints` FAILED: `clippy::infinite_iter` (deny by default) on my new test's `lock.cycle().last()`, which reads the accessor name `cycle` as the iterator adapter; a false positive, repaired by binding the slice first |
| `bash tools/gate.sh`, after the repair | 420 s | exit 0 in 19 s: `check`, `guard-lints`, `guard-doctests` all ok |
| `cargo test -p holonics --test acoustic_wave_port`, after the repair | 420 s | exit 0, 17 passed, 19 s of tests, 42 s wall with the build; the unit run above predates only a comment edit in `hnn/mod.rs` |

The gate's remaining clippy warnings (`manual_is_multiple_of` and others in `tests/acoustic_wave_port.rs` and the notebook files) are
the ones `origin/main` already carries; this change adds none.

### 15.4 Recorded failures checked

- **A search hit is not a join** (lessons): the owners are called at their consumers and equal the old readings on the
  bank; the hand comparisons that stood beside them (`landed >= 4`, `div_euclid`, `net / RAYS`, two `debug_assert`s) are
  deleted. The only hand law left is the test oracle in `dynamic_section::tests::by_hand` and the fixture helper
  `section_lock::tests::symbol`, which agree with the owner's reading and cross-check it.
- **A located cause carried unrepaired into a new consumer**: the cause (the carry law restated beside its owner) is
  repaired in its three consumers, not carried into `concat` or `winding`, which are built on `land` and `Reading::add`.
- **A design thought in arrays and offsets**: the word is stated by its start class, net lift and landing class (a
  residue and its carry), and the cuts of the bank words are a declared grid, not a search.
- **A refusal answered with a larger limit**: none occurred; no deadline was raised.

### 15.5 Not claimed, and owed to #62

That the section is a helical code: no strand face, pairing involution or decoder was built, and `SectionWord::concat`
joins symbol words only. That the junction law holds beyond the quarter-turn grain.

8. The Lean statement of the section-word instance of the carry cocycle: for section words `u`, `v` with `e(u) = c_v`,
   `⌊(c_u + N_u + N_v)/4⌋ = ⌊(c_u + N_u)/4⌋ + ⌊(c_v + N_v)/4⌋` (an instance of `Aeon/Clock/Winding.windings_add` at the
   junction phase `c_v/4`), the refusal at a class mismatch, and `Σ crossing = W` over an admitted word (the telescoped
   recursion).
