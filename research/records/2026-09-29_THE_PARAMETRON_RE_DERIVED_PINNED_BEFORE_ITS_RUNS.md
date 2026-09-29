# The parametron re-derived, pinned before its runs

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the pins; [measured] for the development reads (§5), which used the development
seed `2_026_092_941` and the owner's unit tests only.

**Occasion.** Brandon authorized re-deriving the parametron: "please do not restrict us to clearly
partially implemented constructs." Two located causes meet in it:
- the order repair's blocker: a linear readout of superposed, spectrally placed cells cannot
  separate them, and reading their relative phases (the cross-spectrum) needs a square-law reading
  ([record](2026-09-29_THE_ORDER_REPAIR_ORDER_REACHES_THE_SECTION_ON_KNOWN_TRUTH_AND_TEXT_STAYS_AT_THE_BYTE_MARGINAL.md) §5);
- the certified step's item 4: a linear step through a pumped resonator is refused until its
  Floquet growth bound exists (#62).

## 1. The recorded failures this work could repeat, and how each is avoided

- **An authored routine standing in for learning** (failure 1; "No catered machinery"). The bank
  could be written as a routine that subtracts two cells' symbols. It is not: no code path forms a
  class from symbols. Each member's reading is the growth of its own pumped monodromy, decided by
  its Floquet certificate, and the class is the index of the member that locks. The terrain's truth
  is the terrain's exact routine, which the law admits, and only the harness's comparison reads it,
  after the bank has read.
- **An uncertified step** (failure 5; lesson 6). The certificate is decided by inertia and trusts
  nothing of how its metric was attained. `hnn::constitution` is not edited: another worker is
  tightening the certified step there. A step through a pumped resonator stays refused until the
  constitution reads the bound. This loop states the consumer equation and exposes the bound; it
  builds no new consumer on that owner.
- **A refusal answered with a larger limit** (failure 9; lesson 9). Each run is projected and
  bounded (§6), and a run that reaches its bound is reported incomplete and is not rerun larger.
- **Rings are not a search**
  ([ring-search record](2026-09-28_THE_RINGS_AS_A_SEARCH_FOR_KEYS_PINNED_BEFORE_THE_RUN.md) §8). That
  record located that "the lock does no search": the pump amplified an in-phase pattern the linear
  integration had already formed, and a linear bank has no mechanism by which one lock excludes
  another. The bank here is a receiver of one relative phase, not a key search. Its new element is
  the cells entering the pump, which the ring-search bank never had. The linear lock is kept as a
  control to measure what the old lock reads.
- **Thinking in the programming language** (lesson 11). The design is stated as reflections
  composing into turns, multipliers placed about circles, and a residue's phase on the mode of the
  period's factor 4 (the Chinese remainder theorem's character). On the order-2 terrain the pairs
  `(t − 2, t)` are the terrain's question to a known-truth reader, not a table of offsets inside
  the machine.
- **One construction across modalities** (lesson 2). The bank reads carriers on a ring's mode and
  nothing of a codec. Any modality whose cells are placed as carriers on a ring is read by the same
  bank, and the quarter-turn carrier chart is these terrains' declared placement.
- **Seen material graded as unseen; bits read as progress** (failures 6 and 7). Nothing is learned
  in this loop, so no split is graded, and no bits are reported: the readings are exact counts and
  certified growths.
- **A located cause carried into a new consumer** (failure 3; lesson 3). The order repair's cause
  lives in the prediction readout. This loop builds no consumer on it. It builds the square-law
  reading in the ring's owner and tests it on known truth.

## 2. What is built (the build commit)

- `hnn::ring`:
  - `PumpSchedule`: the pump as a periodic modulation of the constitution, declared or modulated
    by the crossing cells;
  - `ResonatorOperands::scheduled`;
  - `Floquet` (`of`, `placement`, `certify`, `decide`, `bound`), `attain_metric`,
    `FloquetCertificate`, `FloquetReading` and `FloquetBound::reach`;
  - `lock` and `LockedSheets`;
  - `ReceivingBank` and `BankReading`.

  `HnnError` gains `UncertifiedFloquet` and `Polynomial`. Nine tests are in
  `hnn/tests/floquet.rs`.
- Lean `HNN/Floquet` (23 theorems) and `Objects/ParametronLock` (21 theorems).
- The guide's §5, the operator contract row, THE_MACHINE's row and the atlas rows
  (`parametron.pump-schedule` … `parametron.rotating-pump-resonance`).

## 3. Acceptance 1: the Floquet certificate on declared rings

**The declarations.** Every ring has `C = I`, `D = 0`, the port `Y = 16`, the hop `h = 1`, and
its pump's axis `1`. The node is one complex node with `K = I`. The cycle of three is the grounded
cycle, `K = ½I + L` with `L` the cycle's unit Laplacian, realified; its softest node mode is the
constant one at `k₀ = ½`, so its standing bifurcation is `p = 1/4`.

| Ring | Pump step | Strength | Declared side |
|---|---|---|---|
| node | standing | `3/8` | passive |
| node | standing | `1/2` | the edge (the standing bifurcation, `k − 2p = 0`) |
| node | standing | `5/8` | growing |
| node | quarter turn | `1/16` | passive |
| node | quarter turn | `1/4` | growing |
| node | half turn | `1` | passive |
| cycle of three | standing | `1/8` | passive |
| cycle of three | standing | `1/4` | the edge |
| cycle of three | standing | `3/8` | growing |
| cycle of three | quarter turn | `1/32` | passive |
| cycle of three | quarter turn | `1/8` | growing |
| cycle of three | half turn | `1/4` | passive |
| cycle of three | half turn | `3/8` | growing |

Each ring is decided by `Floquet::decide` at the grain `2^(−8)`, on the exact law and on the lattice
word's certified charts (`WordLattice::by_rule(16, 6, 6, 4)`). Each runs an executed passage of 8
periods from the declared seed (node 0's real displacement `1`, its imaginary rate `1/2`) on both.

**It holds when:**
- every passive ring is certified at `ρ = 1`;
- every growing ring is certified with `lower > 1` and a certificate `ρ = upper`;
- each standing bifurcation reads the edge on the exact law;
- every executed tick's balance closes.

[agent-inferred] The criterion applies to the lattice word except at an edge. There a multiplier sits
exactly on the unit circle, and the chart's deviation from the law may move it to either side. The
lattice word's reading of an edge ring is reported, not pinned.

**Beside it**, the bifurcation strengths of the three rotating pumps are bracketed by exact
bisection at `2^(−8)`, with both ends certified: the node's quarter-turn pump in
`(1/16, 1/4]`, and the cycle's quarter-turn in `(1/32, 1/8]` and half-turn in `(1/4, 3/8]`.

## 4. Acceptance 2: the bank reads a relative phase on known truth

**The bank.** One node (`C = I`, `K = I`, `Y = 16`, `h = 1`, `D = 0`) and four members at the
declared pump phases: axis `1`, steps `i^j` for `j = 0, 1, 2, 3`, strength `p = 5/8`, decided at
the grain `2^(−6)`. The two cells crossing the section modulate each member's pump, one tick a
crossing, so member `j`'s carriers are `(c_e, i^j c_l)`. The bank's class is its one locked member,
with every other member certified silent.

[agent-inferred] **The strength is in the lock window.** The aligned member's two ticks are the
standing pump's, so it grows exactly past `p = 1/2` (the proved standing bifurcation). The nearest
misaligned members start to grow in `(361/512, 725/1024]` (§5). `p = 5/8` lies between.

**The placement.** The receiving ring has the order repair's period `D = 60 = 3·4·5` and the mode
`k = 15`, the character of its factor 4. There a cell of symbol `x` at residue `r` arrives with the
carrier `i^(x + r mod 4)`: the cell's carrier transported to its residue.

**The terrains.**
- **T1, the declared pair terrain** (`Draw::new(2_026_092_951)`, fresh), 2,048 pairs. Each pair
  draws `x_e, x_l` below 4 and two distinct residues below 60, and orders them by residue. The truth
  is `(x_e + r_e − x_l − r_l) mod 4`.
- **T2, the order-2 terrain's placed cells.** These are the order repair's 256 evaluated draws
  (`hnn_prediction`'s `order_pairs` at seed `2_026_092_902`: 40 request cells below 4, then 8
  stations `x_t = x_(t−2) + 1 mod 4`). Each cell sits at the residue `t`, and every pair
  `(t − 2, t)` is read: 11,776 pairs.
  - [disclosure] The 2,048 pairs whose later cell is a station all have truth class `1`, so a
    constant reader passes there.
  - The 9,728 request pairs have uniform truths.

**The controls**, on the same pairs:
- **(C1) the bank with the cells out of its pump.** The members' pumps are unmodulated, so this is
  one reading, the same for every pair.
- **(C2) the linear lock.** Two standing parametrons at `p = 5/8` with axes `1` and `i` are seeded
  on the displacement by the sum of the two placed carriers. Each sheet is read after 12 periods, or
  held on the quadrature line. The count is its best fixed map from its sheet patterns to classes,
  computed on the same pairs: the ceiling of any fixed map of that reading.
- **(C3) the best constant class.**

**It holds when** the bank reads the class of every pair exactly: 2,048 of 2,048 on T1 and 11,776
of 11,776 on T2, with no pair left without a class.

**Beside it:**
- the controls' counts;
- the order repair's linear readout, 866 of 2,048. That is a different quantity (the stations of a
  continuation, not the relative classes of placed pairs), reported beside it as the brief asks, not
  compared as like.

**The falsifier.** A pair read wrong or left without a class refutes, at these declarations, that
the bank reads a relative phase's class exactly. The receipt then says so, with that pair's member
readings.

**What this does not claim.**
- No generation: both cells are placed, and nothing is predicted.
- No superposition: each cell pumps its own tick (its section crossing), and the bank does not read
  the superposed moment. The reading of a superposed passage, whose monodromy through every crossing
  cell's pump reads the passage's spectrum at the ring's parametric resonance, is not built.
- The linear lock is not set up to be beaten. No linear threshold reads a relative phase
  (`HNN/Floquet.no_linear_threshold_reads_relative_phase`), and its ceiling is measured to show that
  parity.

## 5. The development reads (before this pin)

- **The lock window** (`hnn_parametron -- develop`). By exact bisection at `2^(−8)`, the members
  whose carriers are a quarter turn apart (and three quarters) start to grow in
  `(361/512, 725/1024]`; the member a half turn apart starts in `(1535/1024, 769/512]`.
- **Time.** 64 development pairs were read serially in 1,728 ms, all 64 exactly. Three node
  decisions took 14 ms, and one cycle-of-three quarter-turn decision on the law and the lattice word
  took 3,866 ms. The peak resident set was 8,269,824 bytes.
- **The unit tests** (`hnn/tests/floquet.rs`) read all sixteen pairs of quarter-turn cells exactly
  with no placement.

No declaration of §3 or §4 was changed after these reads.

## 6. The projections and the stops

| Run | Projection | Memory |
|---|---|---|
| `rings` | the 6 node rings in under 100 ms; the 7 cycle rings at about 4,000 ms each; the brackets' bisections by placement and their 6 certified ends about 15,000 ms: **about 60,000 ms** | under 200,000,000 bytes |
| `bank` | 13,824 bank reads at about 27 ms each serially (about 373,000 ms), on the host's 24 cores **about 30,000 ms**; the linear control's 27,648 locks small beside it | under 500,000,000 bytes |

Each mode stops at 600,000 ms, checked between chunks of 256 pairs, and each process is bounded
externally at 660 s. A run that reaches either bound is reported incomplete and is not rerun with a
larger bound. The commands:

```sh
cargo run --release -p holonics --example hnn_parametron -- rings
cargo run --release -p holonics --example hnn_parametron -- bank
```
