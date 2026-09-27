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
cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 8 declared
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

**Campaign 2's tree on the card** (the receiving parametron's landmark tree mirrored by
`holonics_cuda::hnn::tree::CardTree`: every window's splits in cell order and every deposit's
opened-path update on the card, the class faces completed on the host; the compare phase under the
hardware law, `hnn::reference::compare_phase`). Its wall time is read on the development windows
alone (the deadline stops before the held-out range, so no held-out cell is read), and the card's
line prints the tree's parts:

```sh
flock .local/gpu.lock cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 2479 realization card
```

Receipt of September 26 (2,479 windows over the 4,958 development cells, every window deposited,
no held-out target scored; the RTX 4080 SUPER; wall times exterior, integer ms or µs, a window's
mean as the quotient and remainder over 2,479): the readout outside the wall times and the traffic
is identical, line for line (2,660 lines), to campaign 1's code on the same windows (commit
`7d93b291`), and the mirror's founded count equalled the host tree's after every deposit. The
exposure took 238,149 ms (`96 rem 165` ms a window)
against campaign 1's 284,760 ms (`114 rem 2154`). By phase, campaign 1 → campaign 2, per window:
the compare phase (holon and covector) `29 rem 2236` → `10 rem 1687` ms (`compare_phase`: the tree
at the grain beside the mixture score and the Holon ratio); the tree read (the campaign 1 phase: the
tree faces and the combined faces) `1665 rem 253` → `1674 rem 770` µs, with the tree's transfers
`92 rem 782` µs apart and the deposits' mirror updates `279 rem 1187` µs (their transfers
included); the word's refine read `2034 rem 1065` → `2029 rem 1102` µs; the host's deposit
(`Constitution::deposited`, the normal laws) `50 rem 1023` → `50 rem 917` ms, now the largest
phase. The tree's own parts over every read (compare and re-read: 9,916 phases, 4,958 cells
deposited), per window: the card's reads `153 rem 647` µs, the host's class faces from the splits
`212 rem 77` µs, the combined faces in `ℚ(θ)` (`ReceivingPhases::combine`) `2914 rem 299` µs, the
transfers `347 rem 811` µs, the updates' launches `96 rem 1378` µs. The combined faces, not the
tree, now hold the tree read's time.

**The standing real cut** (THE_REBUILD Decision 23; campaign 1's `Cut` row). `standing_cut.py`
reads the private exposure dataset (`holonics.conversation-exposure.v1`) and writes the pinned cut
and its manifest to `.local/cuts/`. Scope and counts only: the dataset's 24,768 occurrence families
split at its temporal cut into 22,449 development, 617 evaluation and 1,702 deferred; the
development stream is 15,462,581 bytes; the cut is its last 6,148 cells (`n*`), the final 1,190
held out, and the evaluation partition is not read (it stays unspent for step 8's splits).
`cut-file <path>` runs campaign 1's exposure on it, reading the held-out range from the manifest;
the pinned public text is the notebook's development control. The cut's hashes are recorded in #73.

**The wide cut** (THE_REBUILD Decision 35). `standing_cut.py wide 1048576` writes the development
stream's last `2^20` cells, the final `2^17` held out (one eighth), to `.local/cuts/wide-real-cut.*`
(mode 0600), with the whole cut's, the development part's and the held-out part's hashes in its
manifest. It holds the standing cut as its tail, so the standing cut's cells (development and
held out alike) lie in the wide cut's held-out range, and the evaluation partition stays unread.
`2^20` is the largest power of two within the memory cap (`hnn_landmark -- … wide`, stage 0).

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

`hnn_landmark.rs` measures the landmark tree (THE_REBUILD Decision 28, count-only;
`holonics::hnn::landmark`) on the standing cut, executed on its declared dyadic lattice: every path
face and stop weight a numerator of `2^(−M_p)`, every count a half-unit integer, every β an odd/odd
ratio of `W` bits with its exponent, all formed in `u128`, the widths derived from `n*`, `L_R`, the
digits `B` and the depth `D`. The grain `L_R` and `|A|` are campaign 1's field's, declared at the
cut's population. The tree (the cell's binary odometer digits, each predicted at its dyadic cell and
mixed over the preceding cells) chooses its address depth on the development cells only
(`choose_depth`: `D` rises from 1 while the development code length decreases strictly, charged
`⌈log₂⌉` of the family tried). Then `prequential` scores every cell, development and held-out, at
the current standing before its own deposit, and deposits it, for the tree and the online baselines
over the same cells in the same order. It prints each coder's bits a cell at the grain on both
populations, the tree's strict orderings against order-0, order-1 and PPM-2 (disjoint exact
enclosures, or undecided with the overlap), the widths, the β chart's rebases and drift, the rule's
bound and the largest certified per-cell residual, the hot path's wall times (the passage alone, one
all-class face read, a clone), and the executed face's cost against the reference oracle
(`oracle_cost`: the ideal tree weighting in ℚ at the reference width `W_o`), cell by cell:

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
```

Its `letters` mode is campaign 2's development harness (Decision 31): on the development cells
alone (the manifest's held-out range is cut away before anything is read), the tree addressed by
typed bundles (each tick's cell with its declared rings' phase classes, read by the clock-only
replay `hnn::receiving::clock_letters`, the resident's clock law with its key location and
re-keying at each carry-out, without the wave) against the cell-only tree, prequentially. It tries
every nonempty set of campaign 1's four rings at one declared grain (the ring's period, its own
port chart; or its parametron's half-turn sheet, 2): 30 families, each with its own depth sweep,
each charged `⌈log₂(30 + 1)⌉ = 5` bits for the family plus `⌈log₂⌉` of its depths tried, and
prints each family's sweep, `Δ_tree = L_(tree+letters) − L_(tree, cells) + description` and its
uncharged difference, and the choice:

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters
```

`letters contacts` adds the contact families: every set of campaign 1's four contacts whose code
fits the bundle's 32 bits, each contact's letter its owner's reading (`hnn::contact::ContactReading`:
its lock address at the bounds `LockDeclaration::derived` gives, the horizon `∏_(j>r) d_j` of each
ring, times its site kind). The lock
addresses read the clocks alone; the site kinds read the learned constitution, so the harness first
runs the exposure's development part on the host (`Reference::campaign_one().with_deadline(…)`, its
deadline the development's last window, so no held-out cell is read, and only its constitution
curve's contact site readings are read), and the register holds each commit's kinds from the
window after it (the resident refreshes after each ingest). Beside every family it runs the
**constant-slot controls** (`LetterFamily::constant_control`: `r` slots reading one letter at every
tick; `LetterFamily::new` refuses a slot of one letter, so a control is never a declared family and
never charged): they carry no information, so their difference from the cell-only tree is the
enlarged tree's own reweighting, and a family's letters are credited only with `Δ_letters =
L_(tree+letters) − L_(control, r slots) + description`. It checks every enlarged tree's passage bound
(Lean `cell_only_dominance_with_feature_charge`: within one bit a dyadic cell opened of the cell-only
tree at its depth, plus both trees' certified drift). The choice is the least charged family with
both `Δ_tree < 0` and `Δ_letters < 0` decided, the cell-only family otherwise:

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters contacts
```

Its `prior` mode is Decision 32's stop-prior decision. On the development cells alone (the
manifest's held-out range is cut away before the sweep reads anything), the cell-only tree runs under
every law of the declared family (`hnn::landmark::prior_family`: the global dyadic ladder
`w = 1 − 2^(−j)`, `j = 1, …, J`, then the per-depth pairs `(j_root, j_below)`, `j_root ≠ j_below`,
with `J = ⌈log₂(n* B)⌉` from `ladder_top`), each law with its own depth sweep, charged `⌈log₂⌉` of
its depths, and the choice charged `⌈log₂⌉` of the laws (`choose_prior`). It prints each law's code
length and its difference from the `½` tree, the choice, and where campaign 2's constant-slot
controls found their bits: every law's code split by dyadic cell, the two-law joins with the `½`
tree (within `[Σ_h min, Σ_h min + |H|]`) by law and by digit level, and the least law in every
dyadic cell. Then the held-out pass runs once, for the chosen law, against order-0, order-1, PPM-2
and the `½` tree:

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior
```

Its `local` mode is Decision 34's development decision (weighing is local). On the development cells
alone, the receiver's tree (`D = 4`, `½`), every law of Decision 32's family and every member of
Decision 33's Born family are read prequentially, each digit's split before its cell's deposit
(these per-digit splits are this harness's exterior measurement; no owner retains them). It prints
the oracles `Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T` at the digit, cell and dyadic-cell grains, each an exact
enclosure (the units' products of observed sides compare exactly on the tree's lattice), then the
three local laws, each prequential, charged `⌈log₂⌉` of its family and refused when its oracle's
gain does not exceed its price: at each landmark (`Landmarks::local` under every rung, the Born
members' digit splits as the external face), in each digit tree (`FaceJoins` on the laws' executed
digit faces: `½` against each other law at the incumbent's rungs, and two balanced families) and
across epochs (`Mixture::switching` of the tree's and each Born member's cell faces at every rate,
beside Decision 30's plain mixture, with the exact Viterbi dominance bound). A held-out pass runs
once only for a law whose charged development code lies below the tree:

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin local
```

Its `wide` mode is Decision 35's pass on the wide cut (above), given the standing cut, which must
be its tail. The laws are the standing cut's choices: no family is swept again at this scale. Every
code is a population's faces' product enclosed once (`landmark::PassageCode`). In order:
- **0. the memory**: the `½` tree's live bytes a node and the baselines' a cell, measured on the
  standing cut by the harness's counted allocator; the resident bound
  `3 (n B D + 2^B − 1)` bytes a node `+ n` bytes a cell (the tree and the two-law stop mixture's
  two trees at the a-priori node bound, and the baselines) at the standing cut's `D = 4`, for
  every power of two the development stream holds; the largest within Brandon's 20 GB cap, which
  the pinned cut must be; and at that population the deepest depth within the cap, which bounds
  the depth sweep (`choose_depth_within`);
- **1. the depth** on the development cells;
- **2. one prequential passage** over the whole cut at that depth, every cell scored before its
  own deposit: the `½` tree (its widths, operand bits, rebases, releases, drift, rule, largest
  certified residual, nodes and live bytes: the scale checks), Decision 34's adopted law (`½`
  joined per digit tree with `(1, 3)` at `π_½ = ½`, the owner's `StopMixture`, charged `⌈log₂⌉` of
  the 4,082-member family it was chosen from on the standing cut and the depth's bits), and the
  baselines;
- **3. the readings** of each coder on the development and held-out cells and on the standing
  cut's two parts within them, in all and a cell at the grain, and **4. the orderings** on the
  development and held-out cells: the adopted law against the `½` tree, and each against order-0,
  order-1 and PPM-2.

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide .local/cuts/standing-real-cut-campaign-1.bin
```

The `converge <standing cut>` mode measures Decision 36 on the wide cut: the landmark tree founded
at its second arrival (`landmark::Founding::SecondArrival`, Lean `HNN/ConvergenceFounding`), where
two paths meet, against Decision 28's `½` tree at `D = 6`. It runs in four stages:
- **0. the memory and the carriers**: the convergence tree's live bytes a founded node on the
  standing cut (its pending records charged to its nodes), its a-priori resident bound
  `2 (n B + 2^B − 1)` node bytes, the same at every depth, and the deepest depth the carriers admit
  at `n*`;
- **1. the depth sweep** on the development cells, `D = 1, 2, …` while the code decreases strictly
  (the owner's `DepthSweep::{decreasing, of}`), with each depth's founded nodes, pending records,
  live bytes (the counted allocator is thread-local, so trees swept together on several workers are
  each counted alone), wall time and code. The depths run in chunks sized so that the chunk's
  a-priori bounds fit the cap, and the choice reads only the depths up to the stop;
- **2. one prequential passage** over the whole cut of the chosen tree, Decision 28's tree at
  `D = 6` and the baselines;
- **3. the readings** and **4. the orderings** on the parts, each charged `⌈log₂⌉` of its depths and
  of the two founding laws.

`probe D,…` runs only the listed depths' development passages, so that the sweep's cost can be stated
before it runs.

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin converge .local/cuts/standing-real-cut-campaign-1.bin
```

`hnn_born.rs` measures the Born receiver (THE_REBUILD Decision 33, `holonics::hnn::born`, Lean
`HNN/BornFace`) on the standing cut's development cells, beside the landmark tree's current law
(the receiver's declaration through `hnn::receiving::landmark_declaration_with`, cell-only, `D =
4`): each cell scored before its own deposit, for the Born face alone, the tree alone and Decision
30's likelihood mixture of the two (`hnn::receiving::Mixture`, `β` stepped by `q_T(x)/q_B(x)` on the
landmark β chart). The declared family is both emissions (`Position`: a pair of operators per digit
position; `Dyadic`: a pair per dyadic cell, the tree's forced split) at every register width
`χ = 2^j`, `j ≤ J`, the cost bound (`14·4^J·B·n_dev ≤ 2^37` complex products a passage: `J = 8`),
stopping before a width the receiver's carrier refuses at the declared population (at `n* = 2^20`
the solve's residual needs 128 bits at `χ = 32`), charged `⌈log₂⌉` of the members tried; each
population's faces are multiplied and enclosed once (`landmark::PassageCode`). The choice is the
least charged development mixture; a held-out pass runs only if it codes below the tree by
disjoint enclosures. It prints each member's widths,
code lengths at the grain, the orderings mixture − tree and Born − tree, `log₂ β`, the receiver's
chart receipts (the solve's refinements and certificate, the preconditioner's refreshes, the
state's rebases) and the wall time a digit:

```sh
cargo run --release -p holonics --example hnn_born -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
```

Receipt of September 26 (development cells only, 4,958 cells and 39,664 digits; no held-out cell
read; wall times exterior, one host, the run alone): the tree reads `3 + 10/16 + ε` bits a cell
(`18067 + 2/16 + ε` in all). Eighteen members were tried (both emissions, `χ = 1, …, 256`), charged
`⌈log₂ 18⌉ = 5` bits. The Born face alone, bits a cell (`+ ε` each), by `χ = 1, 2, 4, …, 256`:
`Position` `5 + 14/16`, `5 + 14/16`, `5 + 12/16`, `5 + 8/16`, `5 + 2/16`, `4 + 13/16`, `4 + 9/16`,
`4 + 9/16`, `4 + 7/16`; `Dyadic` `4 + 13/16`, `4 + 13/16`, `4 + 14/16`, `4 + 10/16`, `4 + 8/16`,
`4 + 6/16`, `4 + 5/16`, `4 + 3/16`, `4 + 4/16`. The least is `Dyadic`, `χ = 128`: Born − tree
(charged) `2780 + 8/16 + ε` bits in all, `8/16 + ε` a cell, and `log₂ β` ends at `2775 + 8/16 + ε`.
Every member's mixture codes above the tree by disjoint enclosures, mixture − tree (charged)
`6 + 0/16 + ε` in all for all eighteen: the mixture's own `½` prior bit plus the charge, as the
telescope `∏ q = ½W_T + ½W_B` gives when `L_B > L_T`. The least charged mixture is `Dyadic`,
`χ = 16`; no member codes below the tree, so no held-out pass ran. The charts: every solve certified
within at most 4 refinements, the largest certificate below `2^(−C)`, no preconditioner refresh, and
a build with overflow checks reproduced every reading. A digit costs, `Dyadic`: `17 rem 5712 over
39664` µs at `χ = 16`, `365 rem 14640 over 39664` µs at `χ = 128`, `1253 rem 22008 over 39664` µs
at `χ = 256` (`Position` `1175 rem 6800 over 39664`); the harness took 168,717 ms.

`exterior.rs` is the notebook's shared exterior boundary: the cut file and its manifest
(`read_cut`, `manifest_number`), the process's resident set (`resident_set`, read from the
kernel's status for the `wide` mode's receipt) and the exact presentation of
readings. `hnn_exposure`, `hnn_diagnose`, `hnn_landmark` and `hnn_born` include it by `#[path]`.

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
| `hnn_lattice_growth.rs growth` | The deposited constitution's exact bits after each deposit under the budgeted lattice law (precision `k_m = 2⌊log₂ m⌋ + 1` at the locus's deposit clock since its founding), split into lattice entries, carried remainders and solved charts, with the widest carried remainder, the residuals each deposit releases and their bits, the entries whose lattice coordinate moved, the wall time of each refine, compare and deposit with the projected wall time of an exposure of `n*` cells and of the declared population, and (at the first aeons) the largest move of the admitted logits between `Θ` and `Θ + r`, in grains | Budgeted law under Decision 27's receiving law (receipts of September 25, this tree: the receiving map by the prox step, the receiving parametron's region class masses beside it; Decision 26's and the earlier laws' receipts are in git history). **`growth chain 128 declared`** (the chain control, declared steps, 128 deposits): the bits rise and level off near 29,000 (1,011 at the mount, 16,063 at 16, 25,247 at 64, 28,870 at 128: entries 7,416, remainders 16,684 on 516 carried entries, solved 4,770); the widest remainder 51 bits; 22 aeon boundaries release no locus and leave the bits unchanged; 39,189 residuals released over the 128 deposits (3,300,441 bits; reported, never retained); per refine 2 rem 60 over 128 ms, per compare 9 rem 93 over 128 ms and per deposit 11 rem 60 over 128 ms; the carried remainders move the admitted logits by `0`, `275/512`, `1123509/2^22`, `4623/2^20`, `4979521/2^24` and `20386641/2^24` of a grain at the first six boundaries: above one grain at the sixth only (`1 rem 3609425 over 2^24` grains, `\|Δf\|` reading `0 + 1/16 + ε` at `L_R = 16`), where Decision 26's law passed one grain at four of the six (the word-level certificate is owed, #62). **`growth campaign 40 declared`** (campaign 1's declared field over the pinned cut, `fed5488c…:docs/plans/THE_REBUILD.md`, 171,754 bytes; declared steps, 40 deposits): 388,880 → 388,882 → 931,522 → 1,135,697 → 1,211,919 bits at the mount and deposits 1, 16, 32, 40, against `B_Θ = 2^33` (the class masses' prior takes 197,376 of the mount's 321,048 entry bits: 257 regions of 256 masses `1/2`, each `1 + 2` bits; at 40: entries 527,151, remainders 481,647 on 16,421 carried entries, the widest 45 bits, solved charts 203,121); the deposits 4, 16, 32 and 40 release 14,986, 15,690, 15,920 and 15,928 residuals of 1,448,673, 1,660,783, 1,696,533 and 1,696,102 bits (595,419 residuals and 62,121,716 bits over the 40; reported, never retained); no aeon boundary within 40 deposits; per refine 12 rem 30 over 40 ms, per compare 17 rem 11 over 40 ms and per deposit 77 rem 38 over 40 ms, so `n* = 6,148` cells (3,074 windows) project to 331,915 rem 6 over 40 ms (4,730 ms for the 40 deposits). Superseded, with no command in this tree (an earlier law, or the live file before the cut was pinned): the exact law on the chain control, 1,126 → 10,883 → 623,415 bits over two deposits (249 s for the second); the lattice with the remainders released at the aeon collapse; campaign 1 on the live file of 194,092 bytes; and both receipts before the lattice word, whose sizes and wall times were recorded only as decimals (git history) |
| `hnn_lattice_growth.rs equality` | The integral chart's equality with the termwise rational arithmetic, on the real cases: at every deposit each update recomputed over `Rat` alone (`ΔH`, `ΔW`, `Δh_x`, `Δx` with `Ratio`'s product), the carry's accounting `x' + r' + e = x + r + Δ` checked on every carried entry, each normal law's solved chart checked against its certificate (Decision 24: the exact left residual `‖1 − X̂H‖∞` at most the chart's certified `δ`), counted on an unmoved and on a moved Gram, and the receiving parametron's landmark deposit exactly (Decision 28): the staged steps are one per target of the window, in cell order, each at its phase's causal address, and the published tree has passed exactly those cells more (Decision 27's class-mass check, below, is its superseded predecessor) | Every value equal (receipts of September 25, this tree, under Decision 27's receiving law). **`equality chain 8 declared`**: 4,752 carried entries, 32 solved charts certified on an unmoved Gram and 8 on a moved one, 160 class masses exact (189 ms). **`equality chain 32 declared`** (the chain control, 32 deposits at the declared steps): 19,008 carried entries (594 a deposit), 160 solved charts certified, 107 on an unmoved Gram and 53 on a moved one, 640 class masses exact (20 a deposit: the chain's 5 regions of 4 classes) (867 ms). **`equality chain 32 normal`** (the factor steps off): 19,008 carried entries, 118 solved charts on an unmoved Gram and 42 on a moved one, 640 class masses exact (770 ms). **`equality campaign 8 declared`** (campaign 1 on the pinned cut, 8 deposits at the declared steps): 760,648 carried entries (95,081 a deposit), 12 solved charts certified on an unmoved Gram and 36 on a moved one, 526,336 class masses exact (65,792 a deposit: 257 regions of 256 classes) (2,412 ms). The earlier laws' receipts are in git history |
| `hnn_lattice_growth.rs openness` | Campaign 1's source-to-receiver path attenuation `2^(−Σ_a β_a Q_a/2)` within the receiver's last epoch against its grain `1/L_R` (review C2) | **`openness configurations`**: open at 4,328 of the 5,005 phase configurations of the four rings. **`openness uniform`**: open on 2,627 of the 3,074 receiving windows of `n* = 6,148` uniform bytes (SplitMix64 from seed 0). **`openness cut`**: open on 73,740 of the 85,877 receiving windows of the pinned cut (the ratio `73740/85877` is reduced). Superseded, with no command in this tree: 83,703 of 97,046 on the live file of 194,092 bytes, and 2,607 of 3,074 on an unrecorded uniform draw |
| `hnn_exposure.rs` | Campaign 1's exposure protocol (design (d)) on the standing real cut (`cut-file`) or the public development control, and its complete readout (design (f)). It prints the bits on the training and held-out targets against uniform, order-0 and order-1 KT and PPM of order 2, with the verdict against order-0; the model's face is the mixture of the landmark tree's face and the combined face (the primary's ruling A); beside it, the tree face alone (Decision 28: the receiving parametron's tree at each cell's causal address read at the grain, no wave, at the model's constitution and address, from the compare's receipt) and the combined face alone (tree plus wave), each baseline against them, and the combined face against the tree (the wave's contribution); the course by aeon (each aeon's model, tree and combined code lengths and the mixture's `log₂ β` at its boundary) and the mixture's end (`log₂ β`, rebases, drift). Every window is compared and then deposited, held-out windows included (Decision 29). It prints `Kt` with the published keys against the literal over the cells read. Per key location, it prints each ring's fibre, orbits, fallback, failing loop, candidates, propagation work and re-keying jump. Per aeon, it prints the length, lift points, readings, epochs, collapse, the first law (exchange, deposition, total and change, each checked to telescope) and the face against the literal (`code + gain = literal`, checked). It prints the state and constitution bits per source bit with and without the collapse, the constitution's curve by carrier per commit, the budget stop or deadline, the work counted, the executed word's readout (Decision 24: the declared precisions, the charts' refinements with their starts, steps and largest certificate, the remainders the words and their returns released, and the tick balances' residuals against their certified bounds), and the host's wall time by phase (refine read, release, compare read, tree transfer, tree read, holon and covector, `pull_back`, `compose`, `deposited`, tree deposit, re-read and ingest, with the rest of the exposure; on the card, the tree's parts), with the host's tree read per window against the word's (the refine read) | **After the review (September 26; the window scored in cell order, the tree alone on its exact face):** held out (1,190 cells) the model reads `3671 + 9/16 + ε` bits (a cell `3 + 1/16 + ε`), the tree's exact face `3677 + 12/16 + ε`, the tree at the grain `3678 + 2/16 + ε`, the combined face `3671 + 9/16 + ε`; model − order-0 `−1996 + 12/16 + ε`, model − order-1 `−1494 + 11/16 + ε`, model − PPM-2 `−252 + 5/16 + ε`, `L_C − L_T` and `L_model − L_T` each `−7 + 13/16 + ε` bits in all (development `−19 + 12/16 + ε` and `−18 + 12/16 + ε`); `log₂ β` at the aeon boundaries `−2 + 9/16`, `−8 + 10/16`, `−12 + 2/16`, `−17 + 2/16`, `−21 + 0/16`, `−25 + 9/16` at the end (each `+ ε`); host 399,911 ms, card 353,499 ms, the readouts identical line for line (3,303 lines) outside the wall times and the traffic ([record](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md)). The receipts before the review, which read the tree alone at the grain and one `β` a window: receipts of September 26, this tree, prequential (Decision 29), on the standing real cut (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all`, then with `realization card`; 3,074 windows, 3,074 deposits, complete, no budget stop), bits a cell at `L_R = 16`, held out (1,190 cells) and development (4,958): **Decision 28's receiving face with the mixture (ruling A)**: the model `3 + 1/16 + ε` and `3 + 10/16 + ε`, the tree face alone `3 + 1/16 + ε` and `3 + 10/16 + ε`, the combined face `13 + 10/16 + ε` and `8 + 2/16 + ε`, online order-0 `4 + 12/16 + ε` and `4 + 15/16 + ε`, order-1 `4 + 5/16 + ε` and `5 + 1/16 + ε`, PPM-2 `3 + 4/16 + ε` and `3 + 12/16 + ε`; held out in all, model − order-0 `−1989 + 1/16 + ε` (the campaign criterion met), model − tree `−1 + 9/16 + ε`, combined − tree `12606 + 5/16 + ε`; `log₂ β = 35109 + 9/16 + ε` at the end (`W = 28`, 6,146 rebases, drift `5843235441809495541881131462031789/2^126` bits); host 471,824 ms, card 376,507 ms, the readouts identical line for line (3,281 lines) outside the wall times and the traffic. **With the indexed normalized open (ruling B)**: the model, the tree face alone and the combined face each `3 + 1/16 + ε` held out and `3 + 10/16 + ε` on development; held out in all, model − tree `−7 + 1/16 + ε` (development `−18 + 9/16 + ε`), combined − tree `−7 + 1/16 + ε`, model − order-0 `−1996 + 9/16 + ε`, model − order-1 `−1494 + 8/16 + ε`, model − PPM-2 `−252 + 1/16 + ε`; by aeon (the course), combined − tree `−1 + 3/16`, `−6 + 0/16`, `−5 + 3/16`, `−6 + 13/16`, `−6 + 9/16`, `−4 + 12/16` and `log₂ β` `−2 + 12/16`, `−7 + 2/16`, `−12 + 11/16`, `−17 + 5/16`, `−22 + 11/16`, `−25 + 6/16` (each `+ ε`; `W = 28`, 6,146 rebases, drift `11686470883619335088690741741329703/2^127` bits); `|describe|` 1,431 bits, `Kt` `23176 + 10/16 + ε` against the literal 49,184; the constitution 4,722,117 bits; host 405,500 ms (131 rem 2806 over 3,074 a window), card 355,065 ms (115 rem 1555 over 3,074), the readouts identical line for line (3,289 lines) outside the wall times and the traffic. The host's tree read per window: 1,720 µs against the card's word (refine read) at 2,110 µs (a #76 debt). The enclosures' exact endpoints are in the print. The earlier laws' and trees' smokes and receipts (Decision 27's among them) are in git history. **The host realization on the standing real cut** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 24`, run from the repository root, 24 windows on 24 workers): 6,729 → 1,352 ms a window. Per window, before → after: refine read 453 → 198, release 21 → 9, compare read 452 → 0 (the compare takes the refine's kept read), holon and covector 16 → 9, `pull_back` 1,420 → 253, `compose` 2,597 → 479, `deposited` 1,238 → 147, re-read 494 → 218, ingest 0 → 0, the rest 33 → 35. The readout outside the wall times is identical, line for line, to the tree before the change (the bits and code lengths, `Kt`, the constitution's curve, the state and the work). **Campaign 1's first-law exposure** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all`, 3,074 windows; 477,915 ms on the host in the resident exposure's receipt below): its receipt is recorded in #73. **The lattice word** (Decision 24): below the table |
| `hnn_diagnose.rs` | Campaign 1's located failure on the standing real cut (review E1): campaign 1's protocol step for step through the port (held-out windows discarded, not the prequential exposure's), with the decoder's, learning's, the keys' and the source's readings between its methods. Under Decision 28 its decoder readings take the landmark tree's grain logits at each phase's causal address out of the machine's face and read the wave alone | Not rerun under Decision 27. Receipt of September 25, under the receiving law before Decision 26 (at `13d6bb92`; `hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin`, 614 s for the exposure; its rerun with the exact print reads the same values). The exposure's bits reproduce exactly (held-out `7 + 9/16 + ε` against order-0 KT `4 + 12/16 + ε`, bits a cell at `L_R = 16`). Held out, bits a cell through the machine's face: the declared prior's reading `R_0 z` alone `10 + 9/16 + ε`, the machine `7 + 9/16 + ε`, the learned part alone `6 + 11/16 + ε`, the least-squares oracle `R = y wᵀ` on the machine's own features `5 + 0/16 + ε` (`4 + 15/16 + ε` in-sample), the static order-0 face `4 + 12/16 + ε`. The prior's reading holds a share in `[51/56, 3713/4077]` of the held-out logits' energy; `Σh = 141 + ε`, `ε ∈ [2871/3571, 3154/3923]`, against `ln det H_T ∈ [62482/407, 621904/4051]`, below it by `[30317/2588, 26768/2285]`; the constant's reach from ring 2's dormant mode lies in `[3255/4057, 1108/1381]`. Keys: the truth in the fibre on 128 of 128 synthetic cribs; on the cut every fibre empty and the best injective partial closure within its shuffles at 15 of 16 ring-locations. Source: online KT given `τ_0 mod 5` `4 + 14/16 + ε` and given the whole configuration `7 + 12/16 + ε`, against order-0's `4 + 12/16 + ε`; the recent cells a median `1/132` of the source ring's current bin. The reading is the [located-failure record](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md) |
| `hnn_landmark.rs` | The landmark tree (Decision 28, count-only; `hnn::landmark`) on the standing real cut, executed on its declared dyadic lattice: the depth sweep on the development cells, then the prequential run of the tree (its executed lattice face) and the online baselines (uniform, order-0 and order-1 KT, PPM of order 2) over the same cells in the same order, every cell scored before its own deposit; the tree's strict ordering against order-0, order-1 and PPM-2; the derived widths, the β chart's rebases and drift, the rule's bound and the largest certified per-cell residual; the hot path's wall times; the executed face's cost against the reference oracle (the ideal tree weighting in ℚ), cell by cell; `prior`: Decision 32's stop-prior decision on the development cells (every law of the declared family with its own depth sweep, charged), where campaign 2's constant-slot controls found their bits, and the held-out pass once for the chosen law; `local`: Decision 34's oracles at the digit, cell and dyadic-cell grains and its three local laws (at each landmark, in each digit tree, across epochs) on the development cells, charged, with one held-out pass for each law that codes below the tree; `wide`: Decision 35's pass on the wide cut (the memory's derivation, the depth, then one prequential passage of the `½` tree, Decision 34's adopted law and the baselines, read on the development and held-out cells and the standing cut's parts, and ordered); `converge`: Decision 36's convergence founding on the wide cut (the memory and the carriers' admission, the cost probe, the depth sweep of the tree founded at the second arrival with each depth's nodes, pending records, live bytes and wall time, then one prequential passage of the chosen tree, Decision 28's `½` tree at `D = 6` and the baselines, read on the parts and ordered) | **Decision 36's convergence founding** (`hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin converge .local/cuts/standing-real-cut-campaign-1.bin`; September 26; the wide cut, development 917,504 = `2^17·7` cells, held out the final 131,072 = `2^17`; `n* = 2^20`, `L_R = 16`, `B = 8`; bits at the grain, each `+ ε`, exact enclosures). **The memory and the carriers**: on the standing cut the convergence-founded tree at `D = 6` founds 20,514 nodes and holds 26,382 pending first arrivals in 4,131,412 live bytes (202 bytes a founded node, the pending records charged to them); a passage founds at most `n B + 2^B − 1 = 8388863` nodes and holds at most `n B = 8388608` pending records at every depth, a resident bound of 3,389,100,652 bytes at every depth, within the 20 GB cap; the carriers admit `D ≤ 73` at `n*` (`M_p = 62`, `W = 43`, the largest operand 127 bits). **The cost, stated before the sweep** (`… converge … probe 6,12,24`, 50,033 ms): development passages of 12,205, 18,317 and 19,372 ms, founded nodes levelling (3,409,859 at `D = 12`, 3,597,947 at `D = 24`); a serial sweep to `D = 73` would take at most 73 such passages (`73 · 19372 = 1414156` ms), so it ran five depths at once (`⌊20·10^9/3389100652⌋ = 5` trees at the a-priori bound, each counted alone on its worker by the thread-local counter): 4 chunks, 72,120 ms. **The depth** (development, bits in all, `D = 1, …, 20`): `3433804 + 4/16`, `2716633 + 9/16`, `2152956 + 2/16`, `1916443 + 9/16`, `1856891 + 11/16`, `1841335 + 3/16`, `1833763 + 0/16`, `1830634 + 13/16`, `1828577 + 14/16`, `1827901 + 13/16`, `1827448 + 4/16`, `1827348 + 10/16`, `1827279 + 1/16`, `1827258 + 4/16`, `1827211 + 14/16`, `1827199 + 5/16`, `1827197 + 7/16`, `1827193 + 0/16`, `1827190 + 13/16`, `1827191 + 8/16` (above `D = 19`, decided): **`D = 19`**, charged `⌈log₂ 20⌉ = 5` depth bits and `⌈log₂ 2⌉ = 1` for the founding law. Founded nodes 8,646, 69,900, 246,411, 569,438, 1,037,859, 1,580,412, 2,100,875, 2,544,950, 2,889,388, 3,137,243, 3,303,988, 3,409,859, 3,475,298, 3,515,422, 3,540,063, 3,555,658, 3,566,370, 3,574,188, 3,580,220, 3,585,039; pending records 1,401 at `D = 1` to 3,702,226 at `D = 19`; live bytes 1,788,100, 14,289,172, 33,032,548, 132,123,060 (`D = 4, 5`), 264,243,796 (`D = 6`), then 528,485,028 to 528,486,068 (`D = 7..20`, the table's power-of-two capacity); a passage 3,563 ms at `D = 1` to 20,751 ms at `D = 20`. **Against Decision 28's `½` tree at `D = 6`**, both read in one whole-cut passage (the convergence tree's development code equals the sweep's): development `1827190 + 13/16` against `1822006 + 1/16`; charged 6 bits against 4 (`⌈log₂ 6⌉` for Decision 35's depths and the founding bit), the convergence tree lies **above** by `5186 + 12/16` (uncharged `5184 + 12/16`): **the development cells choose Decision 28's founding at the first arrival**. **Held out** (131,072 cells, once): the convergence tree `261125 + 0/16` (`1 + 15/16` a cell), Decision 28's tree `261616 + 4/16`, PPM-2 `395598 + 8/16`, order-1 `496687 + 2/16`, order-0 `631713 + 1/16`; the convergence tree charged 6 bits lies **below** Decision 28's charged 4 by `−490 + 11/16` (uncharged `−492 + 11/16`), below PPM-2 by `−134468 + 7/16` (a cell `−2 + 15/16`), order-1 by `−235557 + 14/16` and order-0 by `−370583 + 15/16`, each decided by disjoint exact enclosures; on the standing cut's held-out part it reads `2385 + 2/16` against Decision 28's `2408 + 9/16`. **The scale checks** (the whole passage): the convergence tree at `D = 19` founds 4,091,017 nodes and holds 4,237,673 pending records, 208,414,756 stored bits and 671,092,356 live bytes (`164 rem 165568 over 4091017` a node) in 21,267 ms, against Decision 28's 5,110,443 nodes, 129,708,315 stored bits, 914,360,948 live bytes and 17,445 ms; its largest `u128` operand 127 bits, 53,320,535 β rebases (1,048,398 at the most-rebased node), 192 carrier releases (`R = 86`), the largest node drift `1808141319/2^46` bits, the rule's bound a cell `4651452039175/2^48` bits (below `1/L_R`) and the largest certified per-cell residual `39027026149/2^48` bits, within it. **What it located**: the path grows one depth a recurrence (a node meets arrivals only while its parent is present, Lean `HNN/ConvergenceFounding`'s conditional note), so on the passage's early cells the convergence tree reads shallower than a tree founded to `D` at the first arrival and codes above it; on the held-out tail, where contexts have recurred, its deeper landmarks code below it with fewer live bytes. The harness 112,898 ms; the process's resident peak 2,189,045,760 bytes. **Decision 35's wide cut** (`hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide .local/cuts/standing-real-cut-campaign-1.bin`; September 26; `2^20` = 1,048,576 cells, held out 917,504..1,048,576 (`2^17` = 131,072 cells, one eighth) from the manifest, development 917,504 = `2^17·7` cells and 7,340,032 digits; `n* = 2^20`, `L_R = 16`, `B = 8`; bits at the grain, each `+ ε`, exact enclosures). **The memory**: on the standing cut the `½` tree at `D = 4` holds 63,320 nodes in 8,260,020 live bytes, 131 bytes a node (`130 rem 28420 over 63320`), the baselines 50 bytes a cell (`49 rem 3396 over 6148`); the resident bound `3 (n B D + 2^B − 1)` bytes a node `+ n` bytes a cell at `D = 4` reads 13,183,468,546 bytes at `2^20`, within Brandon's 20 GB cap, and 26,366,837,298 at `2^21`, above it: `2^20` is the largest power of two within the cap, and at `2^20` the depth is capped at `D ≤ 6` (`D = 7` bounds 23,032,025,537 bytes). **The depth** (development, 51,066 ms): bits a cell `3 + 11/16`, `2 + 15/16`, `2 + 5/16`, `2 + 1/16`, `2 + 0/16`, `1 + 15/16` for `D = 1..6` (`1822006 + 1/16` in all at `D = 6`), strictly decreasing to the cap: `D = 6`, charged 3 bits; the widths (`M_p`, `W`, `C`) from 50, 31, 81 at `D = 1` to 55, 36, 91 at `D = 6`. An uncapped probe (not a receipt) kept decreasing to `D = 16` (`1801976 + 15/16`): the cap binds. **Decision 32's family at scale** (an earlier full run, stopped after this stage and not repeated: 529 laws, `J = ⌈log₂(2^20 · 8)⌉ = 23`, each with its own sweep within `D ≤ 6`, 2,561,831 ms on 17 workers, resident peak 9,423,376,384 bytes): every law chose `D = 6`, and `½` lies strictly below all 528 others by disjoint enclosures, the nearest `(2, 1)` at `+136 + 11/16`, then `(3, 1)` at `+281 + 10/16`, the global rung `j = 2` at `+6746 + 12/16`: `½` is still first at scale. **One passage at `D = 6`** (every cell scored before its own deposit). The `½` tree's scale checks: the largest `u128` operand 127 bits; 5,110,443 nodes, 129,708,315 stored bits and 914,360,948 live bytes (`178 rem 4702094 over 5110443` a node, above the 131 measured on the standing cut; the bound's a-priori 50,331,903 nodes a tree at 131 bytes, 6,593,479,293 bytes, hold it); 43,968,100 β rebases (1,048,555 at the most-rebased node) and 1,664 carrier releases (`R = 90`); the largest node drift `22333373133/2^46` bits; the rule's bound a cell `7421708304497/2^48` bits (below `1/32`), the largest certified per-cell residual `7340494295/2^42` bits, within it. **Development** (bits a cell, and in all): the `½` tree `1 + 15/16` (`1822006 + 1/16`), the adopted law `1 + 15/16` (`1820751 + 8/16`), order-0 `4 + 12/16` (`4382811 + 1/16`), order-1 `3 + 12/16` (`3480545 + 7/16`), PPM-2 `2 + 15/16` (`2731136 + 5/16`), uniform 8. **Held out** (131,072 cells): the `½` tree `1 + 15/16` (`261616 + 4/16`), the adopted law `1 + 15/16` (`261566 + 11/16`), order-0 `4 + 13/16` (`631713 + 1/16`), order-1 `3 + 12/16` (`496687 + 2/16`), PPM-2 `3 + 0/16` (`395598 + 8/16`), uniform 8. **The orderings**, each decided by disjoint exact enclosures: Decision 34's adopted law (`½` with `(1, 3)` at `π_½ = ½`), charged 15 bits (`⌈log₂ 4082⌉ = 12` for the family it was chosen from and the depth's 3) against the `½` tree charged its 3, lies **below** it held out by `−38 + 7/16` (uncharged `−50 + 7/16`; a cell `−1 + 15/16`, within one grain) and on development by `−1243 + 7/16` (uncharged `−1255 + 7/16`): the stop mixture's gain transfers and holds out. The `½` tree charged 3 bits lies **below PPM-2** held out by `−133980 + 11/16` (a cell `−2 + 15/16`: more than one bit a cell and less than `1 + 1/16`), below order-1 by `−235068 + 2/16` and order-0 by `−370094 + 3/16`, and on development below PPM-2 by `−909128 + 11/16` (a cell `−1 + 0/16`); the adopted law charged 15 bits lies below PPM-2 held out by `−134017 + 2/16`. **The standing cut's cells** (the wide cut's tail, held out here, read at the wide standing): the `½` tree codes the standing held-out part in `2408 + 9/16` (`2 + 0/16` a cell) against `3677 + 12/16` (`3 + 1/16`) on the standing cut alone, and its lead over PPM-2 there grows from `−246 + 7/16` uncharged to `−1204 + 4/16`; on these cells the adopted law lies **above** the tree, uncharged, by `+2 + 12/16` (the standing held-out part) and `+0 + 15/16` (its development part), each decided: its held-out gain at scale is made on other cells. **Costs**: the harness 109,950 ms: the depth sweep 51,066 ms, the tree's passage 17,324 ms (counted), the adopted law's 39,504 ms (10,220,886 nodes and 264,647,533 stored bits in its 2 trees, 5,927,552 join rebases, no release, the joins' largest drift `202192655467/2^48` bits), the baselines 1,851 ms; the process's resident peak 1,271,214,080 bytes. The same passage built with overflow checks reproduced every enclosure, and on the standing cut as both cuts the mode reproduces Decision 34's held-out receipt (the adopted law charged 15 bits `−7 + 12/16` below the tree and `−249 + 4/16` below PPM-2, the tree `−243 + 7/16` below PPM-2). **Decision 34's development decision** (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin local`; September 26; 4,958 development cells and 39,664 digits, the held-out range cut away before anything is read; bits at `L_R = 16`, each `+ ε`, exact enclosures). The `½` tree reads `18067 + 2/16` (`3 + 10/16` a cell), its depth `D = 4` charged 3 bits common to every law. **The oracles** `Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T` (before any price): the Born members at the digit grain from `−3283 + 7/16` (`Dyadic`, `χ = 1`) to `−4440 + 14/16` (`Position`, `χ = 2`), at the cell grain from `−1271 + 6/16` to `−1531 + 9/16` (`Dyadic`, `χ = 128`, whose face alone reads `4 + 3/16` a cell), at the dyadic-cell grain only `−11 + 0/16` to `−46 + 3/16`; the stop laws at the dyadic-cell grain from `−174 + 12/16` (`(1, 4)`) and `−172 + 2/16` (`(1, 3)`), and the least law in every unit `−2750 + 8/16` (digit), `−1871 + 10/16` (cell), `−244 + 9/16` (dyadic cell, 107 of 154 opened). **At each landmark** (288 members: 18 Born members × rungs `j = 1..16`, charged 9 bits; the price its family charge, the oracle's gain `4439 + 1/16`): the least is `j = 2` with `Dyadic`, `χ = 1` (an order-0 dyadic face mixed into each landmark), `−61 + 11/16` uncharged and `−52 + 11/16` charged below the tree; the other members from `0 + 0/16` to `−55 + 9/16` uncharged; the largest certified residual a cell `3170175577490309307/2^72` bits. **In each digit tree** (4,082 members: `½` against each other law at the incumbent's rungs `j = 1..16`, and the balanced global ladder and whole family, charged 12 bits; the price one bit a dyadic cell opened plus the charge, 166, against the best pair's oracle gain `173 + 3/16`; the least law in every dyadic cell refused, its naming 1,232 bits against `244 + 9/16`): the least is `½` with `(1, 3)` at `π_½ = ½`, `−133 + 7/16` uncharged (campaign 2's one-slot control exactly) and `−121 + 7/16` charged below the tree, strictly below every other member; the balanced ladder `−15 + 13/16`, the balanced family `+21 + 10/16`. **Across epochs** (234 members: 18 Born members × `α = 2^(−j)`, `j = 1..13`, charged 8 bits; the price the best switching sequence's naming, its exact Viterbi dominance bound less the oracle, plus the charge, `1473 + 9/16` against the best member's cell-grain gain `1530 + 6/16`): Decision 30's plain mixture reads `+1 + 0/16` for every member; the least is `α = 2^(−7)` with `Dyadic`, `χ = 256`, `−106 + 9/16` uncharged (its dominance bound `−65 + 2/16`) and `−98 + 9/16` charged below the tree. **Held out** (1,190 cells, once for each of the three; the tree `3677 + 12/16`, order-0 `5666 + 12/16`, order-1 `5164 + 13/16`, PPM-2 `3923 + 4/16`): **only the stop-weight mixture codes below the tree**: `3659 + 8/16` (`3 + 1/16` a cell), charged its 12 bits `−7 + 12/16` below the `½` tree, and charged 15 bits below order-0 by `−1993 + 12/16`, order-1 by `−1491 + 11/16` and PPM-2 by `−249 + 4/16`, each decided; the owner's `StopMixture` reproduces the joins' development code exactly. The node-local law reads `3685 + 15/16`, charged `+17 + 3/16` above the tree, and the switching mixture `3681 + 0/16`, charged `+11 + 4/16` above: their development gains do not hold out. **Costs**: the mixture carries two trees (126,640 nodes, 2,923,100 stored bits against the `½` tree's 63,320 and 1,426,180), its whole passage 122 ms against 41 ms, 37,910 join rebases, the joins' largest drift `172309355861276769/2^68` bits. Wall: the reads 85,174 ms (the Born members together, `Dyadic` `χ = 256` 84,472 ms), node-local 1,941 ms, the joins 10,299 ms, switching 13,286 ms, the held-out pass 62,881 ms, the harness 201,663 ms. **Decision 32's stop-prior decision** (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior`; September 26; 4,958 development cells, the held-out range cut away before the sweep; bits at `L_R = 16`, each `+ ε`): `J = ⌈log₂(6148 · 8)⌉ = 16`, so 256 laws (the global ladder `j = 1..16`, then the pairs `(j_0, j_(≥1))`), the choice charged `⌈log₂ 256⌉ = 8` bits; every law chose `D = 4` of 5 depths tried (3 bits). The `½` tree (`j = 1`) codes `18067 + 2/16` in all (`3 + 10/16` a cell), as Decision 28's sweep. Every other law is decided **above** it by disjoint exact enclosures: the global rungs `j = 2` by `68 + 1/16`, `j = 3` by `325 + 11/16`, rising to `j = 16` by `2063 + 7/16`; the per-depth laws from `(1, 2)` by `32 + 7/16` to `(15, 16)` by `2032 + 15/16`. **The choice: `½`**, strictly below every other law; charged 11 bits (8 + 3). **Where the constant-slot controls found their bits** (development, 154 dyadic cells opened; the `½` tree's dyadic cells sum to its code length): the control of `r` slots is the per-depth law `(1, r + 1)` joined with the `½` tree per dyadic cell (the test `landmark_constant_slots_are_the_per_depth_prior`, exact in ℚ), and a join codes within `[Σ_h min, Σ_h min + 154]`: `Σ_h min(L_(½,h), L_(law,h)) − L_½` is `−150 + 11/16` for `(1, 2)` (below `½` at 98 dyadic cells), `−172 + 2/16` for `(1, 3)` (91), `−174 + 12/16` for `(1, 4)` (89), `−168 + 6/16` for `(1, 5)` (86), each enclosing campaign 2's measured control (`−114 + 2/16`, `−133 + 7/16`, `−131 + 7/16`, `−124 + 10/16`). By digit level the least join gains at every level (level 0 `−54 + 5/16`, 1 of 1 dyadic cell; level 7 `−27 + 5/16`, 31 of 63), so the preference is per digit tree, not per depth or level; the least law in every dyadic cell reads `−244 + 9/16` uncharged, and naming it costs 8 bits a dyadic cell. **Held out** (1,190 cells, once, the chosen law at `D = 4`): `3 + 1/16` a cell, identical to the `½` tree; charged 11 bits, below order-0 by `−1979 + 15/16` (a cell `−2 + 5/16`), order-1 by `−1477 + 14/16` (`−2 + 12/16`), PPM-2 by `−235 + 7/16` (`−1 + 12/16`), each decided; against the `½` tree charged its 3 bits, above by the family's 8 bits. Wall: the sweep 16,873 ms (256 laws together on 24 workers), the dyadic split 22,628 ms, the held-out pass 488 ms (tree and baselines) and 225 ms (the `½` tree). **Campaign 2's development harness** (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters`; September 26; 4,958 development cells, no held-out cell read; bits in all at `L_R = 16`, each `+ ε`): the cell-only tree reproduces its sweep (`D = 4`, `18067 + 2/16`, `3` depth bits). Every one of the 30 clock-only families chose `D = 4` and is charged 8 bits (`5 + ⌈log₂ 5⌉`); every `Δ_tree` is decided **positive** by disjoint exact enclosures: at the period grains from `42 + 5/16` (rings 2 and 3) to `46 + 6/16` (rings 1 and 3), at the sheet grain from `16 + 12/16` (ring 2; uncharged `8 + 12/16`) to `34 + 0/16` (rings 1 and 3); the least charged family (ring 2's sheet) lies above the cell-only tree by `[1327838923698184517193391047693/2^96, 1327838923698184517193391057605/2^96]` bits. **The choice: the cell-only family** (`hnn::receiving::letter_family`); the clock-only phase classes carry no code-length evidence past the join's charge (at most one bit a dyadic cell opened) and their description. The harness ran in 36,678 ms. **Campaign 2's contact letters** (`… letters contacts`; September 26; the same 4,958 development cells, no held-out cell read; bits in all at `L_R = 16`, each `+ ε`): the exposure's development part on the host (2,479 windows, stopped at cell 4,958, 2,480 commits, no budget stop; 311,021 ms) read every contact a **rotation** at every commit, its whole census rotations (`K_a ≻ 0`, `C_a ≻ 0`: contact 0 → 1 ten, 1 → 2 fourteen, 2 → 3 twenty-two, 3 → 0 ten). The derived bounds are `(P, Q) = (1000, 142)` for `0 → 1`, `(142, 12)` for `1 → 2`, `(12, 0)` for `2 → 3` and `(0, 1000)` for `3 → 0`: ring 3 never winds within an aeon, so contacts 2 and 3 always read `Unlocked`, and with the constant kind their letters are constant (one feature code read). 42 families were declared (30 clock-only, 12 contact; three contact sets whose code passes 32 bits are not declarable), each charged `⌈log₂ 43⌉ = 6` bits plus `⌈log₂ 5⌉ = 3` depth bits; every one chose `D = 4`. **The constant-slot controls** (uncharged, against the cell-only tree): one slot `−114 + 2/16`, two `−133 + 7/16`, three `−131 + 7/16`, four `−124 + 10/16`: `r` constant slots after each cell make the stop weight at every cell depth past the first `1 − 2^(−(r+1))` rather than `1/2` (the constant letter's node sees its parent's counts, so `q = ½k + ½(½k + ½Π) = ¾k + ¼Π` at one slot), and the join mixes that tree with the cell tree, so the reweighting alone codes the development cells below the cell-only tree; it is the tree law's, not a letter's. **`Δ_tree`**: the informative contact families are decided **positive**: contact `0 → 1` (22 feature codes read) `45 + 0/16`, `1 → 2` (12 codes) `34 + 9/16`, both `42 + 13/16`, with the constant contacts `29 + 2/16` to `44 + 2/16`; the constant contact families are decided negative, `−105 + 2/16` (contact 2 or 3 alone, exactly the one-slot control's `−114 + 2/16` plus their 9 bits) and `−124 + 7/16` (both). The clock-only families, now charged 9 bits: period grains `43 + 5/16` to `47 + 6/16`, sheet grain `17 + 12/16` to `35 + 0/16`, all positive. **`Δ_letters`** is decided **positive for every family**: the constant contact families by exactly their `9` bits of description (`[8 + 15/16 + ε, 9 + 0/16 + ε]`), the informative contact families by `148 + 7/16` (`1 → 2`) to `176 + 11/16`, the clock-only families by `131 + 9/16` (ring 2's sheet) to `179 + 15/16`. **The choice: the cell-only family**: no letter, clock or contact, codes below the cell-only tree and its slots' control by its description; the lock addresses that vary carry less than the reweighting they ride on, and the site kinds are constant on the passage. The harness ran in 365,572 ms, the development pass included. Receipt of September 26, the lattice tree (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin`; 6,148 cells, held out 4,958..6,148 from the manifest; `n* = 6,148`, `L_R = 16`, `B = 8`). **The widths** by depth (`M_p = ⌈log₂(3 B L_R (2n* + 2)(n* D² + 2D + 1))⌉`, `W = ⌈log₂(12 B L_R n* D²)⌉`, `C = M_p + W`): `D = 1` 35, 24; `D = 2` 37, 26; `D = 3` 38, 27; `D = 4` 39, 28, `C = 67`; `D = 5` 40, 28. **The sweep** (development, 4,958 cells, bits a cell): `D = 1` `4 + 0/16 + ε`, `D = 2` `3 + 12/16 + ε`, `D = 3` `3 + 10/16 + ε` (in all `18152 + 8/16 + ε`), `D = 4` `3 + 10/16 + ε` (`18067 + 2/16 + ε`), `D = 5` `3 + 10/16 + ε` (`18098 + 7/16 + ε`, above `D = 4`): `D = 4`, charged `⌈log₂ 5⌉ = 3` bits. **Held out** (1,190 cells, bits a cell): the tree `3 + 1/16 + ε`, uniform 8, online order-0 KT `4 + 12/16 + ε`, online order-1 KT `4 + 5/16 + ε`, PPM-2 `3 + 4/16 + ε`; the tree, charged its 3 bits, lies **below** order-0 by `−1987 + 15/16 + ε` bits (a cell `−2 + 5/16 + ε`), below order-1 by `−1485 + 14/16 + ε` (a cell `−2 + 12/16 + ε`) and below PPM-2 by `−243 + 7/16 + ε` (a cell `−1 + 12/16 + ε`), each by disjoint exact enclosures: Decision 28's criterion holds on the lattice. **Development** (bits a cell): the tree `3 + 10/16 + ε`, order-0 `4 + 15/16 + ε`, order-1 `5 + 1/16 + ε`, PPM-2 `3 + 12/16 + ε`; the tree below all three (`−6468 + 1/16 + ε`, `−7257 + 12/16 + ε`, `−666 + 10/16 + ε` bits). **The charts**: 63,320 nodes, 1,426,180 stored bits; 122,267 rebases (6,129 at the most-rebased node); the largest node drift certificate `|log₂ β̂ − log₂ β| ≤ 2016117919/2^43` bits; the rule's bound a cell `6192141373081/2^48` bits (below `1/32`); the largest certified per-cell residual at most `19659010511/2^44` bits. **The oracle** (`β` at `W_o = 130` bits, 58,737 rebases, its own rule below `2^(−48)` bits a cell): the executed face's cost over the ideal lies in `[−1490254332995924151010153/2^95, −2980508665991848302007893/2^96]` bits on the development cells and `[−35737173259935118265357/2^92, −142948693039740473060687/2^94]` on the held-out cells, inside `(−2^(−14), 0)` and `(−2^(−16), 0)`; every cell's observed deviation (at most `2584284295/2^48` bits) lay within its certificate. **Wall** (integer ms and µs): the sweep 846 ms; the prequential run 49,653 ms, all of it the baselines' `log2_enclosure` readings (`hnn::reference`), the tree's own prequential run (receive, code length and sum of every cell) 217 ms and its passage alone 42 ms; one all-class face read (256 classes) at the final standing 91 µs, the held-out addresses' 1,190 reads 80,744 µs in all (`67 rem 1014` over 1,190 µs a read); a clone of the final tree 2,065 µs; the oracle's run 10,861 ms. The rational-face tree of the first receipt (its faces about 3,000 bits) took 56,757 ms for the prequential run and 216,970 ms for its two sweeps. A second run reproduced every value outside the wall times |
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
