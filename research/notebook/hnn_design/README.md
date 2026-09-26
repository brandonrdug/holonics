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

The two Rust measurements run the crate's exact host reference (`holonics::hnn::Reference`), which
the Python scripts do not reimplement, as cargo examples of the `holonics` crate. Their integers
outside the law are milliseconds and the declared counts each header derives (the held-out length
from the joint clock's mean aeon). The development control's cut is pinned:
`docs/plans/THE_REBUILD.md` at commit `fed5488ce70eb5ffbc90f2f03d23638be9d69189` (171,754 bytes).
Each example reads it with `git show`, never from the live file.

`hnn_lattice_growth.rs` runs in three modes, which its header states:

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

`hnn_exposure.rs` runs campaign 1's exposure, `Reference::campaign_one().expose(&field, &cut)`, and
prints its complete readout (design (f)) and, exterior, the host's wall time by phase
(`Exposure::wall`). Its header states the declarations:
- The cut is the pinned cut's first `N` cells, with the field declared at that population. The
  default is `N = n* = 6,148`, the control at the standing cut's population. `cells N` sets another `N`, and
  `cells all` takes the whole cut.
- The held-out part is the tail of 1,190 cells, one mean aeon of the joint clock on uniform bytes
  (agent-inferred). `held-out H` declares a tail of `H` cells instead.
- `windows K` sets a deadline (`Reference::with_deadline`): the run stops after `K` receiving
  windows and is reported incomplete at its cell.

```sh
cargo run --release -p holonics --example hnn_exposure -- windows 8
cargo run --release -p holonics --example hnn_exposure
python3 research/notebook/hnn_design/standing_cut.py 6148   # n*, printed by hnn_exposure
cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all
# the same exposure on the card (the device port, holonics_cuda::hnn::Resident), under the GPU lock
flock .local/gpu.lock cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all realization card
```

`hnn_exposure.rs` is also an example of `holonics-cuda` (its build declares `cfg(holonics_card)`),
so `realization card` runs the same protocol through the device port; the default stays the host.

**The standing real cut** (THE_REBUILD Decision 23; campaign 1's `Cut` row). `standing_cut.py`
reads the private exposure dataset (`holonics.conversation-exposure.v1`) and writes the pinned cut
and its manifest to `.local/cuts/`. Scope and counts only: the dataset's 24,768 occurrence families
split at its temporal cut into 22,449 development, 617 evaluation and 1,702 deferred; the
development stream is 15,462,581 bytes; the cut is its last 6,148 cells (`n*`), the final 1,190
held out, and the evaluation partition is not read (it stays unspent for step 8's splits).
`cut-file <path>` runs campaign 1's exposure on it, reading the held-out range from the manifest;
the pinned public text is the notebook's development control. The cut's hashes are recorded in #73.

`hnn_diagnose.rs` locates campaign 1's failure on the standing cut (review E1: the located cause
before campaign 2). It runs the exposure protocol step for step through the host reference's
`ExecutionPort` and reads between the port's methods, so it changes no law and adds no accessor; it
reproduces the exposure's bits first, as its check. Its four sections are the candidate causes:
the decoder (the mean logit vector's static face, the read features' rank and dormant component,
and the least-squares oracle `R = y wᵀ` scored through the machine's own face), learning (per
deposit the exact update of `R` and `E_0` from the carry's accounting, the leverage `zᵀX̂'z` and
the read logits' executed move, the prior's reading `R_0 z` against the learned part, the covector's
phase share, and the bound `Σh ≤ ln det H_T`), the keys (on synthetic cribs generated by the
declared ring with a true key, and on the standing cut the crib's best injective partial closure
against its own shuffles), and the source and encoding (capacity against `n*`, the path's openness,
online KT given the rings' phase classes, the source ring's bins, and the recent cells' share of the
current bin). Its receipt and reading are the
[located-failure record](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md):

```sh
cargo run --release -p holonics --example hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
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
| `hnn_lattice_growth.rs equality` | The integral chart's equality with the termwise rational arithmetic, on the real cases: at every deposit each update recomputed over `Rat` alone (`ΔH`, `ΔW`, `Δh_x`, `Δx` with `Ratio`'s product), the carry's accounting `x' + r' + e = x + r + Δ` checked on every carried entry, and each normal law's solved chart checked against its termwise certified-chart steps (where the carried Gram took `ΔH` exactly) or its carried Gram's inverse | Every value equal. **`equality chain 32 declared`** (the chain control, 32 deposits at the declared steps): 19,008 carried entries, 40 solved charts by certified-chart and 120 on a moved Gram (4.0 s). **`equality chain 32 normal`** (the factor steps off): the same counts, 19,008 carried entries (1.6 s). **`equality campaign 8 declared`** (campaign 1 on the pinned cut, 8 deposits at the declared steps): 760,648 carried entries (95,081 a deposit), 18 solved charts by certified-chart (the 256-wide source port's at every deposit) and 30 on a moved Gram (110 s) |
| `hnn_lattice_growth.rs openness` | Campaign 1's source-to-receiver path attenuation `2^(−Σ_a β_a Q_a/2)` within the receiver's last epoch against its grain `1/L_R` (review C2) | **`openness configurations`**: open at 4,328 of the 5,005 phase configurations of the four rings. **`openness uniform`**: open on 2,627 of the 3,074 receiving windows of `n* = 6,148` uniform bytes (SplitMix64 from seed 0). **`openness cut`**: open on 73,740 of the 85,877 receiving windows of the pinned cut (85.9%). Superseded, with no command in this tree: 83,703 of 97,046 on the live file of 194,092 bytes, and 2,607 of 3,074 on an unrecorded uniform draw |
| `hnn_exposure.rs` | Campaign 1's exposure protocol (design (d)) on the standing real cut (`cut-file`) or the public development control, and its complete readout (design (f)). It prints the bits on the training and held-out targets against uniform, order-0 and order-1 KT and PPM of order 2, with the verdict against order-0. It prints `Kt` with the published keys against the literal over the cells read. Per key location, it prints each ring's fibre, orbits, fallback, failing loop, candidates, propagation work and re-keying jump. Per aeon, it prints the length, lift points, readings, epochs, collapse, the first law (exchange, deposition, total and change, each checked to telescope) and the face against the literal (`code + gain = literal`, checked). It prints the state and constitution bits per source bit with and without the collapse, the constitution's curve by carrier per commit, the budget stop or deadline, the work counted, the executed word's readout (Decision 24: the declared precisions, the charts' refinements with their starts, steps and largest certificate, the remainders the words and their returns released, and the tick balances' residuals against their certified bounds), and the host's wall time by phase (refine read, release, compare read, holon and covector, `pull_back`, `compose`, `deposited`, re-read and ingest, with the rest of the exposure) | Receipt of September 25, this tree. **`windows 8`** (the smoke: the `n*` cut of 6,148 cells, held out 4,958..6,148, deadline 8 windows): incomplete at its deadline at cell 16. 8 windows, 8 deposits, the path open on 8 of 8, and the peak bits inside a word 5,418. On the 16 training targets the model takes [127.768854, 127.768855] bits, against uniform 128, order-0 KT [124.546125, 124.546126], order-1 KT [128.033681, 128.033682] and PPM [131.486469, 131.486470]: above order-0, below the rest. No held-out target is read, no aeon closes and no key is located (the aeons on this text last 920–1,834 cells). The constitution grows from 191,498 to 739,165 bits over 8 deposits (entries 231,487, remainders 235,192, solved 272,486). The dense moment takes 657,931 bits, and the counted state `⌈log₂N(16)⌉` takes 386. `Kt` is [1,511.768854, 1,511.768855] bits (`\|describe\|` 1,369, keys 0, work 15) against a literal of 128. 35.2 s, 4.4 s a window, serial; 7.7 s, 964 ms a window, with the host realization (the reference's header), the readout identical outside the wall times. **The host realization on the standing real cut** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 24`, run from the repository root, 24 windows on 24 workers): 6,729 → 1,352 ms a window. Per window, before → after: refine read 453 → 198, release 21 → 9, compare read 452 → 0 (the compare takes the refine's kept read), holon and covector 16 → 9, `pull_back` 1,420 → 253, `compose` 2,597 → 479, `deposited` 1,238 → 147, re-read 494 → 218, ingest 0 → 0, the rest 33 → 35. The readout outside the wall times is identical, line for line, to the tree before the change (the bits and code lengths, `Kt`, the constitution's curve, the state and the work). **Campaign 1's exposure** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all`, 3,074 windows, about 6 h at `growth campaign 40`'s means): its receipt is recorded in #73. **The lattice word** (Decision 24): below the table |
| `hnn_diagnose.rs` | Campaign 1's located failure on the standing real cut (review E1): the exposure protocol step for step through the port, with the decoder's, learning's, the keys' and the source's readings between its methods | Receipt of September 25, this tree (`hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin`, 614 s for the exposure). The exposure's bits reproduce exactly (held-out 7.577520 against order-0 KT 4.762009). Held out, bits a cell through the machine's face: the declared prior's reading `R_0 z` alone 10.61, the machine 7.58, the learned part alone 6.72, the least-squares oracle `R = y wᵀ` on the machine's own features 5.02 (4.98 in-sample), the static order-0 face 4.77. The prior's reading holds 91.1% of the held-out logits' energy; `Σh` = 141.80 against `ln det H_T ∈ [153.51, 153.53]`; the constant's reach from ring 2's dormant mode 0.802. Keys: the truth in the fibre on 128 of 128 synthetic cribs; on the cut every fibre empty and the best injective partial closure within its shuffles at 15 of 16 ring-locations. Source: online KT given `τ_0 mod 5` 4.881 and given the whole configuration 7.768, against order-0's 4.762; the recent cells 0.76% of the source ring's current bin. The reading is the [located-failure record](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md) |
| `propagation.py` | Ring-key location by propagation over the data → menu map, `d = 7`, against brute force over all 5,040 plugboards | Propagation equals brute force at 322–3,822 steps against 35,280. The fibre holds the truth; a `δ = 1` chain leaves 35–42 members; 16 independent crib pairs pin the rotor-gauge orbit (7 members); a random cut gives an empty fibre |

**The lattice word's receipt** (Decision 24; `crates/holonics/src/hnn/chart.rs`). Every inverse the
word executes is a certified lattice chart, every transient is carried with error feedback, and the
return pulls back through the executed charts' transposes. The run is `hnn_exposure -- cut-file
.local/cuts/standing-real-cut-campaign-1.bin cells all windows 24`, from the repository root, 24
windows on 24 workers. The tree before is `c690f76d`, the exact word.

- **Declared precisions**, by rule: charts on `2^(−38)ℤ`, certificate target `2^(−19)`, transients on
  `2^(−15)ℤ`.
- **Wall time: 1,349 → 129 ms a window**, the two binaries run back to back on the same host.
  Per window, before → after:

  | Phase | Before | After |
  |---|---|---|
  | refine read | 200 | 11 |
  | release | 10 | 0 |
  | compare read | 0 | 0 |
  | holon and covector | 9 | 8 |
  | `pull_back` | 251 | 4 |
  | `compose` | 477 | 3 |
  | `deposited` | 143 | 55 |
  | re-read | 219 | 20 |
  | ingest | 0 | 0 |
  | the rest | 36 | 24 |

  The re-read's 20 ms is a word (about 12 ms) and the Holon ratio's code length (about 8 ms).
- **Bits.** On the 48 training targets the model takes [383.133596, 383.133597] bits, against
  [383.133826, 383.133827] before. The law changed, and the difference is −0.000230 bits over 48
  targets. The verdicts are unchanged: below uniform, above order-0 KT (327.32), order-1 KT and PPM.
- **Kt.** `|Field::describe|` grows from 1,369 to 1,403 bits, because it codes the word's
  precisions. `Kt` goes from [1,768.133826, …] to [1,802.133596, …].
- **Inside the word.** The peak bits of the change fall from 5,649 to 32, and the work's peak bits
  from 18,615 to 60.
- **The constitution's curve** changes only through the deposits' samples: 1,110,084 → 1,108,108
  bits at commit 24. The residuals each deposit releases fall from about 0.17 Gbit to 4.0 Mbit,
  because the returns' covectors now have bounded denominators.
- **The resident** counts the executed charts: 2,426,004 → 2,545,660 bits.
- **Charts.** 384 refinements, 16 a window. The 90 cold starts are the rings after each deposit,
  whose warm certificates were 1.4 to 2.3; none fell back to an exact inverse, where one exact
  inverse of the 26-wide ring took 27.7 ms. 831 rounded Newton–Schulz steps. The largest
  certificate is `526198678409/2^58` (≈ 1.83·10⁻⁶) against the target `2^(−19)` (≈ 1.91·10⁻⁶).
- **Released remainders.** The words released 5,573 nonzero forward remainders (the largest
  `2^(−16)`, ℓ1 sum ≈ 0.0464, 475,823 bits). The returns released 11,936 adjoint remainders (the
  largest `2^(−16)`, ℓ1 sum ≈ 0.0907, 927,125 bits).
- **Balances.** All 72 tick balances close up to their residuals within their certified bounds. The
  largest residual is ≈ 2.19·10⁻⁴, against its bound ≈ 1.63·10⁻³.

**The resident exposure's receipt** (rebuild step 5, Decision 25; `holonics_cuda::hnn::Resident`,
`crates/holonics-cuda/src/hnn/port.rs`). The device port runs every word on the card (the charts'
Newton–Schulz refinement and certificates, the word's open, ticks and receiving read in one launch,
its return in one launch, the moment's ingest) and keeps on the host what the port plan assigns it
(the faces in `ℚ(θ)`, the Holon ratio, the tick balances, the composition, the deposit's prox step,
the ledger, keys and collapse). Run from the repository root on the RTX 4080 SUPER, the host's
command first, then the card's, back to back.

- **Parity.** The readouts are identical line for line outside the wall times: 79 lines at
  `windows 24` and 2,663 lines on the full cut. `holonics-cuda`'s `port_tests.rs` asserts every
  `InteractionReturn` equal in lockstep (the chain control, generic constitutions, campaign 1 on
  drawn bytes, deferred compares, a releasing collapse, refusals, and the standing cut's first 24
  windows).
- **Realization.** The word and its return are each one block of 256 threads (the entry's lowered
  ceiling), four rows a thread over the widest stage (the 1,024 logits).
- **Wall time.** 24 windows: host 120, card 113 ms a window. Full cut (3,074 windows): host
  477,915 ms (155 ms a window), card 334,358 ms (108 ms a window). Per window, host → card:

  | Phase | 24 windows | Full cut |
  |---|---|---|
  | refine read | 11 → 2 | 34 → 3 |
  | release (the card's includes the tick balances, read on the host) | 0 → 2 | 0 → 2 |
  | holon and covector | 8 → 8 | 9 → 9 |
  | `pull_back` | 4 → 1 | 4 → 2 |
  | `compose` | 3 → 3 | 9 → 9 |
  | `deposited` | 47 → 45 | 38 → 39 |
  | re-read (the card's includes the successor's publication) | 20 → 20 | 33 → 17 |
  | ingest | 0 → 0 | 0 → 0 |
  | the rest | 23 → 28 | 24 → 25 |

  What remains is the host's exact arithmetic the port plan keeps there: the deposit's prox step
  (38 ms), the faces' code lengths in `ℚ(θ)` (about 9 ms in the re-read and 9 in the holon), the
  composition (9 ms).
- **Across the bus**, per window on the full cut: 173 kB for the words (plans, operands, records
  with the logits, certificates, moved operators and charts; two words a window), 25 kB for the
  return, 20 kB for the publication's moved words (16 octets each), 56 octets for the ingest. The
  full cut ran before a word's operands crossed as its weights only (its chart slots are gathered on
  the card), which moves 18.7 kB less a word: 220 → 183 kB a window at `windows 24`.
