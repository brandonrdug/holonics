# HNN design measurements

[established-bounded; measured] The exact-arithmetic scripts behind the measured numbers in the
[step 4 design](../../../docs/plans/THE_REBUILD.md#step-4-design-the-hnn-law) and its #62 item on
bounded bit growth ("Step 4 (#73) owed"). Every measured value is a `fractions.Fraction` or an exact
integer, so each number is exact and seeded; `capacity.py` bisects on the exact integer test and
certifies each `n*` at `n* − 1` and `n*`, with no float anywhere. No script prints a float or a decimal
(a decimal is a collapse): `field.exact` prints a short ratio as `n/d (q rem r over d)`, its integer
quotient and remainder, and a long one as its integer quotient `q` plus its remainder's exact
enclosure between continued-fraction convergents with denominators at most `2^12`,
`q + e, e in [a/b, c/d]`, with the exact ratio's size in bits. They need only the Python 3 standard
library. Run one from the repository root:

```sh
python3 research/notebook/hnn_design/power.py
```

The Rust measurements run the crate's exact host reference (`holonics::hnn::Reference`), which
the Python scripts do not reimplement, as cargo examples of the `holonics` crate. Their integers
outside the law are milliseconds and the declared counts each header derives (the held-out length
from the joint clock's mean aeon). They print no float and no decimal:
- bits are enclosures with exact endpoints, read at the receiver's grain `L_R = 16` through
  `GrainCell::of` as `n + k/16 + ε` (the carry `n`, the phase class `k` and the fibre
  `0 ≤ ε < 1/16`, exact);
- a comparison is an exact ordering with the exact difference of the enclosures, read the same way;
- a ratio is reduced, with its integer quotient and remainder;
- a mean of milliseconds is the integer quotient with its remainder, `q rem r over N`.

The receipts below quote the grain cell `n + k/16 + ε`; the exact fibres are in each command's
output. The development control's cut is pinned: `docs/plans/THE_REBUILD.md` at commit
`fed5488ce70eb5ffbc90f2f03d23638be9d69189` (171,754 bytes). Each example reads it with `git show`,
never from the live file.

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
90 s and `capacity.py` about 6 min (375,000 ms in the last run); the rest take seconds.

| Script | What it measures | The design's number it reproduces |
|---|---|---|
| `power.py` | The global power `P` over 8 ticks on six rings of widths 4, 2, 4, 6, 2, 4: the six-cycle plus a chord | Lossless: `P` is constant exactly. Dissipative: `P(t) − P(t+1)` equals the dissipation exactly at every tick. With the contrast port `W_c ≠ 0`: `P(t+1) − P(t) = Π_c` exactly; with dissipation, passive `W_s` and `W_c` together, `P(t+1) − P(t) = −dissipation + (W_s term ≤ 0) + Π_c` exactly at every tick, and `Π_c` takes both signs over 8 starting states. With `W_c` 8 times larger the balance stays exact and `P` grows in 8 ticks by `P(8)/P(0) = 244 + e`, `e in [2626/3871, 251/370]` (an exact ratio of 7,580 bits) |
| `swing_power.py` | The junction Swing's power with one exponent per ring against one per contact | Per ring (not conserved): `73199/1920` (38 rem 239 over 1920) at tick 0, `50 + e`, `e in [3683/3851, 285/298]` at tick 5, `43 + e`, `e in [1577/3270, 1074/2227]` at tick 6. Per contact: `648509/23040` (28 rem 3389 over 23040) at every tick |
| `word_bits.py` | The bits of the change within one word, and the change released or carried from word to word | One word: 77, 482, 1,461, 3,512 and 7,623 bits at 2, 4, 8, 16 and 32 ticks. Released: at most 963 bits over 32 words of 6 ticks. Carried: 11,728, 24,057, 48,707 and 98,004 bits after 8, 16, 32 and 64 words (about 90 s) |
| `critical_cayley.py` | A lossless Cayley storage wave that persists across words | 77 → 6,272 bits over 256 words |
| `bits2.py` | The reaction read from the state or from the sheet class; the local Swing's causal cone; the source moment on a non-closing and on a closing ring; the first design's case (5) | 46 → 804,289 bits in 7 ticks; 44, 85, 127, 209, 374 and 705 bits; rings {0, 2}, then {0, 1, 2, 3, 5}, then all six; 7, 34, 146 and 592 bits; 1, 2, 3, 5, 7 and 9 bits; no collapse 47, 221, 912 and 1,831 bits. It prints the first design's truncation, "3, 5, 7, 7, max 52", under a WITHDRAWN label (R2 C2a) |
| `collapse_check.py` | Case (5) under the spectral projector by a Sylvester solve, and under the certified release | 72, 74, 77, 78, max 121 bits; the certified release refused at 32 of 32 boundaries. Its first line is the withdrawn truncation, labelled so |
| `collapse_bezout.py` | The same spectral projector by Bezout over ℚ[x], independent of the Sylvester solve | 72, 74, 77, 78, max 121 bits |
| `release.py` | The time-indexed causal diamond by the design's two recursions (reach and observe), on a path of six rings (source ring 0, receiving ring 2) | At `A = 2` (`e_last = 3`, `e_max = 4`): 72 of 156 constitution entries released (the separable form releases 44); every released item replaced by arbitrary values leaves every admitted reading identical over 20 injections; replacing any one retained item changes a reading, 12 of 12. The rim case `A = 1` (`e_last = 2`): every element released, 132 of 156; identical readings; 8 of 8 retained items tight |
| `capacity.py` | The capacity `n*` by counting: the least `n` with `N(n) < \|A\|^n`, certified by exact integers at `n* − 1` and `n*`; the moment's dense code as a reading | `n* = 137` on three rings of periods 3, 4, 5 over `\|A\| = 2`; 6,148 cells on campaign 1's declared field; 8,577 for one byte ring of period 7 with `Δ = {1}`; 3,641,698 for eight source rings of period 16 (8,421,376 slots). The dense code: 135 bits at `n = 128` and 138 at 144 on the control; about 117,000 cells for the period-7 ring; for the eight rings, with uniform counts, below the source for good from 4,243,457 cells (the dense code over the source bits `9472/9375` (1 rem 97 over 9375) at `n = 4,200,000`, `132608/134375` at `n = 4,300,000`) |
| `deposit_bits.py` | The bits of a deposited map under the per-locus normal law | `R` at `γ = 1`: 155, 176, 180, 196 bits after 8, 32, 128, 256 deposits; at `γ = 1/2`: 1,001, 5,172, 22,477, 46,784. `E` at `γ = 1`: 612, 3,237, 14,852 bits after 8, 32, 128 deposits |
| `hnn_lattice_growth.rs growth` | The deposited constitution's exact bits after each deposit under the budgeted lattice law (precision `k_m = 2⌊log₂ m⌋ + 1` at the locus's deposit clock since its founding), split into lattice entries, carried remainders and solved charts, with the widest carried remainder, the residuals each deposit releases and their bits, the entries whose lattice coordinate moved, the wall time of each refine, compare and deposit with the projected wall time of an exposure of `n*` cells and of the declared population, and (at the first aeons) the largest move of the admitted logits between `Θ` and `Θ + r`, in grains | Budgeted law (receipts of September 25, this tree, rerun after the lattice word). **`growth chain 128 declared`** (the chain control, declared steps, 128 deposits): the bits rise and level off below 30,000 (16,573 at 16, 26,480 at 64, 29,583 at 128, at most 29,660: entries 7,575, remainders 17,073 on 535 carried entries, solved 4,935); the widest remainder 51 bits; 22 aeon boundaries release no locus and leave the bits unchanged; from deposit 8, 78 deposits each release 401–529 residuals of 27,161–47,617 bits and the other 43 each release 6 residuals of 674–911 bits (reported, never retained); per refine 2 rem 49 over 128 ms, per compare 6 rem 91 over 128 ms and per deposit 8 rem 74 over 128 ms; the carried remainders move the admitted logits by 0, `764483/2^20`, `129/512`, `1220269/2^21`, `4768911/2^24` and `1089145/2^24` of a grain at the first six boundaries (each under one grain: `\|Δf\|` reads `0 + 0/16 + ε` at `L_R = 16`). **`growth campaign 40 declared`** (campaign 1's declared field over the pinned cut, `fed5488c…:docs/plans/THE_REBUILD.md`, 171,754 bytes; declared steps, 40 deposits): 191,504 → 730,262 → 940,225 → 1,017,065 bits at deposits 1, 16, 32, 40 (at 40: entries 333,241, remainders 481,411 on 16,407 carried entries, the widest 45 bits, solved charts 202,413 and still growing as the Grams fill), against `B_Θ = 2^33`; the first deposit moves nothing (no cell has been ingested); from deposit 4 each deposit releases 14,986–15,932 residuals of 1,434,761–1,697,757 bits (reported, never retained); no aeon boundary within 40 deposits; per refine 12 rem 16 over 40 ms, per compare 17 rem 10 over 40 ms and per deposit 79 rem 6 over 40 ms, so `n* = 6,148` cells (3,074 windows) project to 334,451 rem 8 over 40 ms (4,752 ms for the 40 deposits). Superseded, with no command in this tree (an earlier law, or the live file before the cut was pinned): the exact law on the chain control, 1,126 → 10,883 → 623,415 bits over two deposits (249 s for the second); the lattice with the remainders released at the aeon collapse; campaign 1 on the live file of 194,092 bytes; and both receipts before the lattice word, whose sizes and wall times were recorded only as decimals (git history) |
| `hnn_lattice_growth.rs equality` | The integral chart's equality with the termwise rational arithmetic, on the real cases: at every deposit each update recomputed over `Rat` alone (`ΔH`, `ΔW`, `Δh_x`, `Δx` with `Ratio`'s product), the carry's accounting `x' + r' + e = x + r + Δ` checked on every carried entry, and each normal law's solved chart checked against its certificate (Decision 24: the exact left residual `‖1 − X̂H‖∞` at most the chart's certified `δ`), counted on an unmoved and on a moved Gram | Every value equal (receipts of September 25, this tree, rerun after the lattice word). **`equality chain 32 declared`** (the chain control, 32 deposits at the declared steps): 19,008 carried entries, 160 solved charts certified, 107 on an unmoved Gram and 53 on a moved one (703 ms). **`equality chain 32 normal`** (the factor steps off): 19,008 carried entries, 117 solved charts on an unmoved Gram and 43 on a moved one (571 ms). **`equality campaign 8 declared`** (campaign 1 on the pinned cut, 8 deposits at the declared steps): 760,648 carried entries (95,081 a deposit), 12 solved charts certified on an unmoved Gram and 36 on a moved one (2,542 ms). The earlier law's wall times, recorded as decimal seconds, are in git history |
| `hnn_lattice_growth.rs openness` | Campaign 1's source-to-receiver path attenuation `2^(−Σ_a β_a Q_a/2)` within the receiver's last epoch against its grain `1/L_R` (review C2) | **`openness configurations`**: open at 4,328 of the 5,005 phase configurations of the four rings. **`openness uniform`**: open on 2,627 of the 3,074 receiving windows of `n* = 6,148` uniform bytes (SplitMix64 from seed 0). **`openness cut`**: open on 73,740 of the 85,877 receiving windows of the pinned cut (the ratio `73740/85877` is reduced). Superseded, with no command in this tree: 83,703 of 97,046 on the live file of 194,092 bytes, and 2,607 of 3,074 on an unrecorded uniform draw |
| `hnn_exposure.rs` | Campaign 1's exposure protocol (design (d)) on the standing real cut (`cut-file`) or the public development control, and its complete readout (design (f)). It prints the bits on the training and held-out targets against uniform, order-0 and order-1 KT and PPM of order 2, with the verdict against order-0. It prints `Kt` with the published keys against the literal over the cells read. Per key location, it prints each ring's fibre, orbits, fallback, failing loop, candidates, propagation work and re-keying jump. Per aeon, it prints the length, lift points, readings, epochs, collapse, the first law (exchange, deposition, total and change, each checked to telescope) and the face against the literal (`code + gain = literal`, checked). It prints the state and constitution bits per source bit with and without the collapse, the constitution's curve by carrier per commit, the budget stop or deadline, the work counted, the executed word's readout (Decision 24: the declared precisions, the charts' refinements with their starts, steps and largest certificate, the remainders the words and their returns released, and the tick balances' residuals against their certified bounds), and the host's wall time by phase (refine read, release, compare read, holon and covector, `pull_back`, `compose`, `deposited`, re-read and ingest, with the rest of the exposure) | Receipt of September 25, this tree (rerun after the lattice word). **`windows 8`** (the smoke: the `n*` cut of 6,148 cells, held out 4,958..6,148, deadline 8 windows): incomplete at its deadline at cell 16. 8 windows, 8 deposits, the path open on 8 of 8, and the peak bits inside a word 32. On the 16 training targets the model takes exact `[10122890754603364407531975645581/2^96, 10122890754603364407559456235585/2^96]` bits, `127 + 12/16 + ε` at `L_R = 16` (a cell: `7 + 15/16 + ε`), against uniform 128, order-0 KT `124 + 8/16 + ε`, order-1 KT `128 + 0/16 + ε` and PPM `131 + 7/16 + ε`: above order-0 (model − order-0 KT reads `3 + 3/16 + ε`), below the rest (model − uniform `−1 + 12/16 + ε`, model − order-1 KT `−1 + 11/16 + ε`, model − PPM `−4 + 4/16 + ε`). No held-out target is read, no aeon closes and no key is located (the aeons on this text last 920–1,834 cells). The constitution grows from 191,504 to 567,421 bits over 8 deposits (entries 231,568, remainders 234,984, solved 100,869). The dense moment takes 657,931 bits, and the counted state `⌈log₂N(16)⌉` takes 386: per source bit `657931/128` (5140 rem 11 over 128) and `193/64` (3 rem 1 over 64). `Kt` is exact `[122468425199830195115177297222029/2^96, 122468425199830195115204777812033/2^96]` bits, `1545 + 12/16 + ε` (`\|describe\|` 1,403, keys 0, work 15), above the literal of 128 by `1417 + 12/16 + ε`. 1,049 ms, 131 rem 1 over 8 ms a window, with the host realization (the reference's header); the earlier trees' smokes (the exact word, serial and with the host realization) are in git history. **The host realization on the standing real cut** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 24`, run from the repository root, 24 windows on 24 workers): 6,729 → 1,352 ms a window. Per window, before → after: refine read 453 → 198, release 21 → 9, compare read 452 → 0 (the compare takes the refine's kept read), holon and covector 16 → 9, `pull_back` 1,420 → 253, `compose` 2,597 → 479, `deposited` 1,238 → 147, re-read 494 → 218, ingest 0 → 0, the rest 33 → 35. The readout outside the wall times is identical, line for line, to the tree before the change (the bits and code lengths, `Kt`, the constitution's curve, the state and the work). **Campaign 1's exposure** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all`, 3,074 windows; 477,915 ms on the host in the resident exposure's receipt below): its receipt is recorded in #73. **The lattice word** (Decision 24): below the table |
| `hnn_diagnose.rs` | Campaign 1's located failure on the standing real cut (review E1): the exposure protocol step for step through the port, with the decoder's, learning's, the keys' and the source's readings between its methods | Receipt of September 25, this tree (`hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin`, 614 s for the exposure; its rerun with the exact print reads the same values). The exposure's bits reproduce exactly (held-out `7 + 9/16 + ε` against order-0 KT `4 + 12/16 + ε`, bits a cell at `L_R = 16`). Held out, bits a cell through the machine's face: the declared prior's reading `R_0 z` alone `10 + 9/16 + ε`, the machine `7 + 9/16 + ε`, the learned part alone `6 + 11/16 + ε`, the least-squares oracle `R = y wᵀ` on the machine's own features `5 + 0/16 + ε` (`4 + 15/16 + ε` in-sample), the static order-0 face `4 + 12/16 + ε`. The prior's reading holds a share in `[51/56, 3713/4077]` of the held-out logits' energy; `Σh = 141 + ε`, `ε ∈ [2871/3571, 3154/3923]`, against `ln det H_T ∈ [62482/407, 621904/4051]`, below it by `[30317/2588, 26768/2285]`; the constant's reach from ring 2's dormant mode lies in `[3255/4057, 1108/1381]`. Keys: the truth in the fibre on 128 of 128 synthetic cribs; on the cut every fibre empty and the best injective partial closure within its shuffles at 15 of 16 ring-locations. Source: online KT given `τ_0 mod 5` `4 + 14/16 + ε` and given the whole configuration `7 + 12/16 + ε`, against order-0's `4 + 12/16 + ε`; the recent cells a median `1/132` of the source ring's current bin. The reading is the [located-failure record](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md) |
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
- **Bits.** On the 48 training targets the model takes, in this tree's rerun, exact
  `[30354970831364957692165135403267/2^96, 15177485415682478846138748501305/2^95]` bits, which read
  `383 + 2/16 + ε` at `L_R = 16` (the receipt at `53db0a8a` recorded only an outward decimal
  enclosure, which contains it). The exact word's enclosure before lies in the same grain cell and
  above it; it was recorded only as a decimal, so its exact endpoints and the exact difference are
  owed (rerun at `c690f76d`). The law changed.
  The verdicts are unchanged: below uniform, above order-0 KT (`327 + 5/16 + ε`), order-1 KT and
  PPM.
- **Kt.** `|Field::describe|` grows from 1,369 to 1,403 bits, because it codes the word's
  precisions. `Kt` goes from `1768 + 2/16 + ε` (the exact word's; exact endpoints owed, rerun at
  `c690f76d`) to exact `[142779733439106052737404000930051/2^96,
  71389866719553026368758181264697/2^95]` bits, `1802 + 2/16 + ε` (this tree's rerun).
- **Inside the word.** The peak bits of the change fall from 5,649 to 32, and the work's peak bits
  from 18,615 to 60.
- **The constitution's curve** changes only through the deposits' samples: 1,110,084 → 1,108,108
  bits at commit 24. The residuals each deposit releases fall, because the returns' covectors now
  have bounded denominators; both trees' released bits a deposit were recorded only as decimals
  (exact readings owed; rerun at `c690f76d` and `53db0a8a`).
- **The resident** counts the executed charts: 2,426,004 → 2,545,660 bits.
- **Charts.** 384 refinements, 16 a window. The 90 cold starts are the rings after each deposit,
  whose warm certificates were recorded only as decimals (exact readings owed; rerun); none fell
  back to an exact inverse, where one exact inverse of the 26-wide ring took 27,700 µs. 831 rounded
  Newton–Schulz steps. The largest certificate is `526198678409/2^58` against the target
  `2^(−19) = 549755813888/2^58`: below it by `23557135479/2^58`.
- **Released remainders.** The words released 5,573 nonzero forward remainders (the largest
  `2^(−16)`, 475,823 bits) and the returns 11,936 adjoint remainders (the largest `2^(−16)`, 927,125
  bits); their ℓ1 sums were recorded only as decimals (exact readings owed; rerun at `53db0a8a`).
  This tree's rerun (after `41cbd056`) releases 5,573 forward remainders, ℓ1 sum
  `438949721590752728797/2^73`, 476,141 bits, and 11,935 adjoint remainders, ℓ1 sum an exact ratio
  of 831 bits in `[368/4067, 155/1713]`, 926,820 bits.
- **Balances.** All 72 tick balances close up to their residuals within their certified bounds. The
  largest residual and its bound were recorded only as decimals (exact readings owed; rerun at
  `53db0a8a`). This tree's rerun: the largest residual
  `24189175054009847231496313928325525947359/2^147` against its bound
  `145513756276589703458585123821562965016963/2^146`, below it by
  `266838337499169559685673933714800404086567/2^147`.

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
  the card), which moves less a word (the saving in octets: exact reading owed; rerun): 220 → 183
  kB a window at `windows 24`.
