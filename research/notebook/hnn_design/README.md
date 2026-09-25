# HNN design measurements

[established-bounded; measured] The exact-arithmetic scripts behind the measured numbers in the
[step 4 design](../../../docs/plans/THE_REBUILD.md#step-4-design-the-hnn-law) and its #62 item on
bounded bit growth ("Step 4 (#73) owed"). Every measured value is a `fractions.Fraction` or an exact
integer, so each number is exact and seeded; `capacity.py` uses a float only to bracket a bisection,
and certifies each `n*` by exact integers. They need only the Python 3 standard library. Run one
from the repository root:

```sh
python3 research/notebook/hnn_design/power.py
```

`hnn_lattice_growth.rs` is the one Rust measurement: it runs the crate's exact host reference
(`holonics::hnn::Reference`), which the Python scripts do not reimplement, as a cargo example of the
`holonics` crate, in three modes (its header states each). Its only integers outside the law are
milliseconds. The campaign field's cut is pinned: `docs/plans/THE_REBUILD.md` at commit
`fed5488ce70eb5ffbc90f2f03d23638be9d69189` (171,754 bytes), which the example reads with
`git show`, never the live file:

```sh
cargo run --release -p holonics --example hnn_lattice_growth -- growth chain 128 declared
cargo run --release -p holonics --example hnn_lattice_growth -- growth campaign 40 declared
cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 32 declared
cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 32 normal
cargo run --release -p holonics --example hnn_lattice_growth -- equality campaign 8 declared
cargo run --release -p holonics --example hnn_lattice_growth -- openness configurations
cargo run --release -p holonics --example hnn_lattice_growth -- openness uniform
cargo run --release -p holonics --example hnn_lattice_growth -- openness cut
```

`field.py` is the exact reference of the revised tick: the junction Swing (a parallel adaptor), the
Cayley ring element with its passive part `W_s` and its contrast port `W_c` driving inside the
midpoint, the contact's midpoint two-port and the global power. Its defaults (`W_s = W_c = 0`) draw
exactly what the earlier scripts drew. `power.py`, `release.py` and `word_bits.py` import it. The
scripts come from four rounds: the first revision's re-run of the first review's measurements
(`bits2.py`), the second review, R2 (`swing_power.py`, `critical_cayley.py`, `collapse_check.py`),
the second revision (the rest), and the third revision, answering R3 (`power.py`'s contrast-port
cases, the counting `capacity.py` and the time-indexed `release.py`). `word_bits.py` takes about
90 s and `capacity.py` about 3 min; the rest take seconds.

| Script | What it measures | The design's number it reproduces |
|---|---|---|
| `power.py` | The global power `P` over 8 ticks on six rings of widths 4, 2, 4, 6, 2, 4: the six-cycle plus a chord | Lossless: `P` is constant exactly. Dissipative: `P(t) − P(t+1)` equals the dissipation exactly at every tick. With the contrast port `W_c ≠ 0`: `P(t+1) − P(t) = Π_c` exactly; with dissipation, passive `W_s` and `W_c` together, `P(t+1) − P(t) = −dissipation + (W_s term ≤ 0) + Π_c` exactly at every tick, and `Π_c` takes both signs over 8 starting states. With `W_c` 8 times larger the balance stays exact and `P` grows 245-fold in 8 ticks |
| `swing_power.py` | The junction Swing's power with one exponent per ring against one per contact | Per ring: 38.1 → 51.0 → 43.5 (not conserved). Per contact: 28.147 at every tick |
| `word_bits.py` | The bits of the change within one word, and the change released or carried from word to word | One word: 77, 482, 1,461, 3,512 and 7,623 bits at 2, 4, 8, 16 and 32 ticks. Released: at most 963 bits over 32 words of 6 ticks. Carried: 11,728, 24,057, 48,707 and 98,004 bits after 8, 16, 32 and 64 words (about 90 s) |
| `critical_cayley.py` | A lossless Cayley storage wave that persists across words | 77 → 6,272 bits over 256 words |
| `bits2.py` | The reaction read from the state or from the sheet class; the local Swing's causal cone; the source moment on a non-closing and on a closing ring; the first design's case (5) | 46 → 804,289 bits in 7 ticks; 44, 85, 127, 209, 374 and 705 bits; rings {0, 2}, then {0, 1, 2, 3, 5}, then all six; 7, 34, 146 and 592 bits; 1, 2, 3, 5, 7 and 9 bits; no collapse 47, 221, 912 and 1,831 bits. It prints the first design's truncation, "3, 5, 7, 7, max 52", under a WITHDRAWN label (R2 C2a) |
| `collapse_check.py` | Case (5) under the spectral projector by a Sylvester solve, and under the certified release | 72, 74, 77, 78, max 121 bits; the certified release refused at 32 of 32 boundaries. Its first line is the withdrawn truncation, labelled so |
| `collapse_bezout.py` | The same spectral projector by Bezout over ℚ[x], independent of the Sylvester solve | 72, 74, 77, 78, max 121 bits |
| `release.py` | The time-indexed causal diamond by the design's two recursions (reach and observe), on a path of six rings (source ring 0, receiving ring 2) | At `A = 2` (`e_last = 3`, `e_max = 4`): 72 of 156 constitution entries released (the separable form releases 44); every released item replaced by arbitrary values leaves every admitted reading identical over 20 injections; replacing any one retained item changes a reading, 12 of 12. The rim case `A = 1` (`e_last = 2`): every element released, 132 of 156; identical readings; 8 of 8 retained items tight |
| `capacity.py` | The capacity `n*` by counting: the least `n` with `N(n) < \|A\|^n`, certified by exact integers at `n* − 1` and `n*`; the moment's dense code as a reading | `n* = 137` on three rings of periods 3, 4, 5 over `\|A\| = 2`; 6,148 cells on campaign 1's declared field; 8,577 for one byte ring of period 7 with `Δ = {1}`; 3,641,698 for eight source rings of period 16 (8,421,376 slots). The dense code: 135 bits at `n = 128` and 138 at 144 on the control; about 117,000 cells for the period-7 ring; for the eight rings, with uniform counts, below the source for good from 4,243,457 cells (ratio 1.010 at 4.2 × 10⁶, 0.987 at 4.3 × 10⁶) |
| `deposit_bits.py` | The bits of a deposited map under the per-locus normal law | `R` at `γ = 1`: 155, 176, 180, 196 bits after 8, 32, 128, 256 deposits; at `γ = 1/2`: 1,001, 5,172, 22,477, 46,784. `E` at `γ = 1`: 612, 3,237, 14,852 bits after 8, 32, 128 deposits |
| `hnn_lattice_growth.rs growth` | The deposited constitution's exact bits after each deposit under the budgeted lattice law (precision `k_m = 2⌊log₂ m⌋ + 1` at the locus's deposit clock since its founding), split into lattice entries, carried remainders and solved charts, with the widest carried remainder, the residuals each deposit releases and their bits, the entries whose lattice coordinate moved, the wall time of each refine, compare and deposit with the projected wall time of an exposure of `n*` cells and of the declared population, and (at the first aeons) the largest move of the admitted logits between `Θ` and `Θ + r`, in grains | Budgeted law (receipts of September 25, this tree). **`growth chain 128 declared`** (the chain control, declared steps, 128 deposits): the bits rise and level off at 30 kbit (15,681 at 16, 26,247 at 64, 29,899 at 128: entries 7,667, remainders 17,008 on 535 carried entries, solved 5,224); the widest remainder 51 bits; 22 aeon boundaries release no locus and leave the bits unchanged; from deposit 8 each deposit releases 466–529 residuals of 0.16–1.77 Mbit (reported, never retained); 11 ms per refine, 63 ms per compare and 28 ms per deposit on average; the carried remainders move the admitted logits by 0, 0.72, 0.25, 0.58, 0.29 and 0.06 of a grain at the first six boundaries. **`growth campaign 40 declared`** (campaign 1's declared field over the pinned cut, `fed5488c…:docs/plans/THE_REBUILD.md`, 171,754 bytes; declared steps, 40 deposits): 0.19 → 0.95 → 1.26 → 1.37 Mbit at deposits 1, 16, 32, 40 (at 40: entries 0.33 Mbit, remainders 0.48 Mbit on 16,407 carried entries, the widest 45 bits, solved charts 0.56 Mbit and still growing as the Grams fill), against `B_Θ = 2^33`; the first deposit moves nothing (no cell has been ingested); from deposit 4 each deposit releases 15,237–15,932 residuals of 0.12–0.18 Gbit (reported, never retained); no aeon boundary within 40 deposits; 0.49 s per refine, 4.7 s per compare and 1.8 s per deposit on average, so `n* = 6,148` cells (3,074 windows) project to 21,773 s, about 6 h. Superseded, with no command in this tree (an earlier law, or the live file before the cut was pinned): the exact law on the chain control, 1,126 → 10,883 → 623,415 bits over two deposits (249 s for the second); the lattice with the remainders released at the aeon collapse, a sawtooth peaking at 5.5 Mbit, and on campaign 1 0.19 → 250 Mbit over 21 deposits; on the live file of 194,092 bytes, 1.52 Mbit at 56 deposits, 0.52, 5.0 and 7.4 s per refine, compare and deposit, and before the integral chart 6.1 s, 63 s and 28 s at deposit 8 |
| `hnn_lattice_growth.rs equality` | The integral chart's equality with the termwise rational arithmetic, on the real cases: at every deposit each update recomputed over `Rat` alone (`ΔH`, `ΔW`, `Δh_x`, `Δx` with `Ratio`'s product), the carry's accounting `x' + r' + e = x + r + Δ` checked on every carried entry, and each normal law's solved chart checked against its termwise Sherman–Morrison steps (where the carried Gram took `ΔH` exactly) or its carried Gram's inverse | Every value equal. **`equality chain 32 declared`** (the chain control, 32 deposits at the declared steps): 19,008 carried entries, 40 solved charts by Sherman–Morrison and 120 by inversion (4.0 s). **`equality chain 32 normal`** (the factor steps off): the same counts, 19,008 carried entries (1.6 s). **`equality campaign 8 declared`** (campaign 1 on the pinned cut, 8 deposits at the declared steps): 760,648 carried entries (95,081 a deposit), 18 solved charts by Sherman–Morrison (the 256-wide source port's at every deposit) and 30 by inversion (110 s) |
| `hnn_lattice_growth.rs openness` | Campaign 1's source-to-receiver path attenuation `2^(−Σ_a β_a Q_a/2)` within the receiver's last epoch against its grain `1/L_R` (review C2) | **`openness configurations`**: open at 4,328 of the 5,005 phase configurations of the four rings. **`openness uniform`**: open on 2,627 of the 3,074 receiving windows of `n* = 6,148` uniform bytes (SplitMix64 from seed 0). **`openness cut`**: open on 73,740 of the 85,877 receiving windows of the pinned cut (85.9%). Superseded, with no command in this tree: 83,703 of 97,046 on the live file of 194,092 bytes, and 2,607 of 3,074 on an unrecorded uniform draw |
| `propagation.py` | Ring-key location by propagation over the data → menu map, `d = 7`, against brute force over all 5,040 plugboards | Propagation equals brute force at 322–3,822 steps against 35,280. The fibre holds the truth; a `δ = 1` chain leaves 35–42 members; 16 independent crib pairs pin the rotor-gauge orbit (7 members); a random cut gives an empty fibre |
