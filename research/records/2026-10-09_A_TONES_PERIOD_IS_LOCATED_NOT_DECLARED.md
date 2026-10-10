# A tone's period is located, not declared

**Date.** October 9. **Issues.** #148, #73, #386, #62. **Grade.** Definition record, with a
source-inspected account of the owners and a fixed acceptance. The Rust was written against the
read signatures; a delegated worker later compiled and ran `tests/acoustic_encoding.rs` once under
the common compiler lease (§6.1: 7 of 7 passed, no source change). That is a worker's reading, not a
validation-queue receipt. The predictions in §6 come from an independent exact replica (receipts
below), which is not a repository owner.

## 1. The acceptance

[encoder record §5](2026-10-09_THE_HOLONIC_ENCODER_EXPLODES_A_SOURCE_INTO_CO_PRESENT_FRAMES_AND_AN_AXIS_EXPOSES_WITHOUT_AUTHORING_WHEN_NO_RELABELLING_MOVES_IT.md)
fixed, before any build, the first loop of the encoder: the machine locates an undeclared grid width,
and in a second modality, with the same construction, a sampled tone's undeclared period, through
its own encoding. This record is the second modality's first rung: the samples of a tone enter as
`Encoded` through a chart whose period the machine located. Brandon's October 9 scope update
(relayed) governs how far it goes: the part that survives any audio representation is the location
by the machine's own law, and the sample chart below is provisional.

## 2. What the owners do, and where they stop

[source-inspected] **Keys are located on a declared helix.** `compression::keys::transport::TransportLocation`
locates a transport `A(u) ∈ ℤ/D`, injective labels `λ` and a key by loop closure over a read set, on
a `CarryHelix` whose ring periods are declared (the provisional-founding record, §3: "frames ...
declared; nothing live changes them"). It reads only the equality of occurrences, so it takes the
passage's classes and needs no `Encoded` (guard 9 restricts the field's entries, not the location).

[source-inspected] **The field takes exterior data only through a located chart.**
`Encoded::through` refuses every chart the field did not locate (`EncodingError::Unencoded`) and a
plural fibre (`EncodingError::Plural`); a sample "has no path into the field" otherwise (THE_MACHINE
guard 9). So the tone's period must come out of `TransportLocation` before `PassageChart::located`
may be built.

[source-inspected] **The pair law owns an undeclared distance, but only on the admitted passage.**
`hnn::keys::{station_pairs, PairLocation}` read every distance below a source ring's period and
locate the least surviving distance `δ₀` with its map (a class of windings is one key), so the
period of a tone is `δ₀` times the cycle of its map. They consume `Encoded`, so they are the
consumer of what is admitted here, not the admission. `Field::admit` requires the located helix to
be the field's rings in carry order, so the distances visible on that field are below its source
ring's period; reading `δ = 12` there is an owed join.

[finding] **A periodic passage is not generally located on a declared helix.** A passage of period
`P` carries one cycle of information. On a helix rich enough to hold it the fibre is plural (the
replica reads, for the triangle tone of period 7 on rings `(6, 5)`, 47 gauge classes), which the
chart law refuses; on a helix whose odometer digit is not the waveform the fibre is empty (a
quantized triangle of period 12 is empty on every frame wide enough to hold its four levels, 7 of
the 12 frames of rings up to 6; the other 5 are too narrow). A single
declared helix therefore locates a generic tone on no reading. This is what the existing owners
cannot do without a join, and it is a measurement, not a defect to hide.

## 3. The join: frames located by loop closure, a period read from a located cycle

[definition; agent-inferred] The join is two small owners, modality-free (the same construction
reads a text passage, an image row, a tone or a motor word).

**The cycle of a located navigator** (`LocatedTransport::cycle`, `Cycle`). The located transport
steps the lift of its helix, `ℓ_(k+1) = ℓ_k + A(λ(c(ℓ_k)))` on `ℤ/D`, a deterministic map of a
finite set. A key on a cycle returns; the first return is the cycle's length `n`, and the joint
clock turns `Σ_(k<n) A(u_k) = w · D` whole times, the winding `w` (helix = circle + carry). It reads
the located transport and its labels, never a sample.

**The frame family and the period** (`compression::keys::frames`). The machine's frame family is a
declared set of carry helices, declared once for every source, as the rings of a field are. A
passage is located on each frame by the existing loop closure; a frame *carries* it when its fibre
is one gauge class and the least key that regenerates the passage lies on a closed cycle. The
period is the cycle length every carrying frame reads:

```text
period(x) = n   iff   every carrying frame F reads the same cycle n at its key
refused           when no frame carries x (Unlocated, with every frame's typed reading)
                  or the carrying frames read different cycles (Disagree)
```

Frames that do not carry the passage hold their reading, typed: narrow (more classes than receiving
cells), empty (no survivor), plural (several gauge classes), open (one class, key on no cycle). The
bound on the family's rings is its capacity, a ring size; in the tests every ring is shorter than the
tone's period, so the located cycle (7 on rings `(2, 5)`, 12 on `(3, 4)`) is no ring's period and
nothing was read off a ring. (The test on rings up to 9 includes rings of periods 7 and 9: it
witnesses agreement between frames, not that the period was undeclared.)

[proved-derived] **Relabelling.** Location reads only equality (`transport`, "The relabelling law"),
so each frame's reading, cycle and winding on `π∘x` are those on `x`; the test pins it on the
reversed sample alphabet.

## 4. The provisional boundary chart

[provisional; modality boundary only] The tests' `SampleChart` takes exact integer samples at a
declared integer sample clock and reads each distinct value as an ordinal of the alphabet in order
of first occurrence; its decoder returns the exact value. It declares no period, no bin width and no
meaning of a value, and no library type depends on it (it lives in the test file, not in the
library, so that it cannot become the audio representation by use). It is a declared exact-equality
alphabet, not symbols that emerge from dynamics; it is a stand-in for the recovered Holonic Encoder's
audio designs. A float stream would convert at this boundary with its residual stated; that
conversion is not built.

## 5. The consumer equations (asserted in `tests/acoustic_encoding.rs`)

```text
decode(encode x) = x                           exactly, every sample read
c(ℓ_k) = the encoded cell of sample k          the lift is the sample's address
ℓ_(k+1) = ℓ_k + A(u_k)                         with the encoded passage's digits a_g(c)
D E = ρ,  E T_c = U_c E                        at each consuming step (Encoded::check_step)
regenerate(key, n′) = x′                       on samples the location never read
```

The route is `FrameFamily::locate` → `PassageChart::located` → `Encoding::found` →
`Encoded::through`, so the existing squares, the Preimage Fibre and the label invariance are the
owners'. A field declared on the carrying frame's own rings admits the encoded passage
(`Field::admit`).

## 6. Fixed acceptance, and what the replica predicts

The claim is fixed before any run. **The tests** (`cargo test -p holonics --test acoustic_encoding`):
- sawtooth of period 7 (`⌊(k mod 7)/2⌋`, three periods read) on rings up to 6: the located period
  is 7, read from the machine's receipt; each carrying frame admits the samples;
- sawtooth of period 12 (`⌊(k mod 12)/3⌋`, same four levels, three periods read): the located period
  is 12;
- rings up to 9 read period 7 on several frames that agree;
- the Thue–Morse sequence (exact, aperiodic; 128 samples) is refused `Unlocated`, every frame empty
  (guaranteed, not only predicted: it is overlap-free, so no deterministic generator on `ℤ/D` with
  `D ≤ 30` reproduces it);
- five other periodic tones are held or located but never given a wrong period;
- the reversed alphabet moves no reading;
- a field declared on the rings admits the located passage.

[predicted by an independent replica; not run in the repository] The replica
(`receipts/2026-10-09-acoustic-encoding/replica.py`, integers only, output in `replica_predictions.txt`)
re-implements the loop closure, the key fibre and the cycle, and predicts, on rings up to 6:

| source | readings of the 12 frames | cycle read |
|---|---|---|
| sawtooth, period 7 | 5 narrow, 6 plural, 1 one | rings `(2, 5)`: 7, winding 1 (`Σ A = 6 + 4 = 10 = D`) |
| sawtooth, period 12 | 5 narrow, 6 empty, 1 one | rings `(3, 4)`: 12, winding 1 (`A ≡ 1`, `Σ A = 12 = D`) |
| Thue–Morse, 128 | 12 empty | none: refused |
| sawtooth, period 7, rings up to 9 | 9 narrow, 26 plural, 3 one | rings `(2, 5)`, `(2, 7)`, `(2, 9)`: 7 each, winding 1 |
| triangle, period 7 | 5 narrow, 6 plural, 1 one | rings `(2, 5)`: 7, winding 3 |
| square, period 7 | 11 empty, 1 one | rings `(5, 2)`: 7, winding 1 |
| sawtooth step 2, period 8 | 5 narrow, 5 empty, 2 plural | none: held |
| sawtooth step 3, period 9 | 2 narrow, 10 empty | none: held |
| quantized triangle, period 12 | 5 narrow, 7 empty | none: held |

### 6.1 Measured (October 9, one run under the common lease)

[computational-witness; worker's run, not a queue receipt] `cargo test -p holonics --offline -j 2
--test acoustic_encoding -- --test-threads=1 --nocapture`, exit 0, wall 29,086,782,095 ns including a
cold build of the crate and its dependencies, child peak resident 1,879,148 KiB, deadline 300 s. 7 passed, 0 failed, 0 ignored. The readings equal the replica's prediction table
above on every row, tally by tally:

| source | measured tally (narrow, empty, plural, open, one) | cycle read |
|---|---|---|
| sawtooth, period 7, rings to 6 | 5, 0, 6, 0, 1 | rings `(2, 5)`: 7, winding 1 |
| sawtooth, period 12, rings to 6 | 5, 6, 0, 0, 1 | rings `(3, 4)`: 12, winding 1 |
| sawtooth, period 7, rings to 9 | 9, 0, 26, 0, 3 | rings `(2, 5)`, `(2, 7)`, `(2, 9)`: 7 each, winding 1 each |
| triangle, period 7 | 5, 0, 6, 0, 1 | rings `(2, 5)`: 7, winding 3 |
| square, period 7 | 0, 11, 0, 0, 1 | rings `(5, 2)`: 7, winding 1 |
| sawtooth step 2, period 8 | 5, 5, 2, 0, 0 | held (`Unlocated`) |
| sawtooth step 3, period 9 | 2, 10, 0, 0, 0 | held (`Unlocated`) |
| quantized triangle, period 12 | 5, 7, 0, 0, 0 | held (`Unlocated`) |
| Thue–Morse, 128 | 0, 12, 0, 0, 0 | refused (`Unlocated`) |

The reversed alphabet read the same tally and cycle as the original (the relabelling test). The
field declared on the carrying rings admitted the located passage: rings `(2, 5)` read chart
dimension 10, reached 10, founded dimension 9, squares 10 states and 4 transports, 21 cells; rings
`(2, 7)` and `(2, 9)` the same fibre and cells at dimensions 14 and 18; rings `(3, 4)` on period 12
read dimension 12, reached 12, founded 10, a fibre of 2 directions, 36 cells. No prediction failed and
no assertion was edited.

[agent-inferred] **The fixtures were chosen after this measurement, and say so.** The sawtooth is
the waveform that is an odometer's own receiving digit, which is what a helix of coprime rings
generates; tones the family does not carry are held, not tuned until they pass (lesson 12). The
passing claim is therefore narrow: the family locates the tones that are orbits of its navigators,
and refuses the rest with their typed readings.

## 7. Recorded failures checked

- **An authored routine standing in for learning** (failure 1, lesson 5; guard 17). No period
  finder, autocorrelation, transform or peak picker exists. The family is not a list of candidate
  periods; the location is the repository's own loop closure; the only reading of the located
  object is its own first return. The risk remaining is that the family scan is a search over
  frames: each frame is declared before any source, each is located by the same law, and a result
  needs agreement; whether that is learning of a frame, or a catalogue of them, is a review rule.
- **Text as the exception** (failure 3, lesson 2). The construction takes classes and a declared
  family; only `SampleChart` is acoustic.
- **A fixture as the goal** (lesson 12). See §6; the held tones are printed.
- **A design thought in the programming language** (lesson 11). Stated in residues and winding:
  the lift's hidden digits are the local phase, the receiving digit the cell, the winding the carry.
- **A located cause carried unrepaired** (lesson 3). Plural fibres are the located cause here; they
  stay open in their owner (§2) and the family does not average them.

## 8. Recovered laws (relayed October 9): what this design keeps, changes and leaves

1. **Propagation and carry** (July 28 record). *Kept:* the lift is circle plus carry and is never
   reduced to the scalar residue `z^g = 1`: `LocatedTransport::lifts` keeps absolute lifts, `cell(ℓ)`
   is the receiving digit of the unreduced lift, and `Cycle.winding` is the whole carry. The hidden
   rings' digits are the local sample phase, and no Fourier or quadrature phase is used. *Not met:*
   no cell is a polynomial `X_j(z)` of real coefficients and no response is propagated through cells;
   only the carry of the single exact sample per tick is kept.
2. **Timed decoder.** *Kept:* the exact sample clock, an exact decoder (`g·z = q + r` with `q = z`,
   `r = 0` for integer samples), no padding. *Changed:* one `Encoded` cell per occurrence, which is
   the field's current source type. *Not met:* the gain, clipping, remainder and quadrature packing of
   the temporal receiver. `Encoded::decoder` is a class readout, not a PCM decoder.
3. **Multiscale relation `c_next = P(c)`, `r = c − U(c_next)`.** Not used.
4. **Exact butterflies.** Not used. Equivalence here is the located transport `(A, λ, key)`, and no
   claim is made that another recording of the same tone is recruited by it.
5. **Consuming joins.** *Kept exactly:* `PassageChart::located` → `Encoding::found` → `Encoded::through`
   with `E T = U E`, `D E = ρ`, the fibre and label invariance. Quantization after superposition,
   terminal support and decoder-work defect are not exercised (one exact tone, read whole).
6. **The decoder horizon's open square** (decoding the machine's own released motion reproduces the
   admitted receiver consequence with its residual). Untouched.

## 9. Not claimed

- The audio representation: it awaits the recovered Holonic Encoder audio designs. `SampleChart` is
  provisional, declares exact-equality symbols, and is not to be built upon.
- That symbols emerge from dynamics, that waves and particles are one dynamics across modalities, or
  that writing is received as oriented packing over time (Brandon's points): none is built.
- That a generic tone is located (§2, §6), or noise, polyphony, a superposition, or any real
  recording.
- That a finite read determines an unknown source's future, or that the frame family is a generic
  period detector. The cycle itself does not over-read: [agent-inferred; Epime, October 9] on a fully
  labelled closed orbit the lift's first-return length `N` equals the emitted orbit's least period
  `p`, under the owners' own hypotheses (`g = D/cells ≤ D/2`, `c(ℓ) = ⌊ℓ/g⌋`, `λ` injective). `p`
  divides `N` (`Compression/Landmark/Context/Evolution.leastPeriod_dvd`). The advance depends only on
  the emitted class, so each `p`-block advances by the same `S` and `ℓ_(jp) = ℓ_0 + jS (mod D)`.
  These states all emit `ℓ_0`'s class, so by injectivity they lie in one cell, an interval of `g`
  consecutive residues. If `S ≢ 0`, they form a coset of the subgroup of index `h = gcd(S, D) ≤ D/2`,
  whose canonical residues span `D − h ≥ D/2 > g − 1`. That is impossible, so `S ≡ 0`, the lift
  returns after `p`, and `N = p`. Owed (#62) as a Lean statement beside `CarryWord`, whose
  constant-rate reading is not this state-dependent advance.
- The pair-law cross-check at `δ = P` on the admitted passage, and a field derived from the located
  frame (the tests declare it by hand).
- Anything beyond the 7 tests of §6.1, which one worker ran once; they are not a validation-queue
  receipt. Lean for the cycle and the period (#62).

## 10. Owners

`compression::keys::{frames, transport::{LocatedTransport::cycle, Cycle}}` (new);
`hnn::encoding::{PassageChart::located, Encoding, Encoded::through}`, `hnn::field::Field::admit`
(consumed); `tests/acoustic_encoding.rs`; atlas `encoding.located-period`.
