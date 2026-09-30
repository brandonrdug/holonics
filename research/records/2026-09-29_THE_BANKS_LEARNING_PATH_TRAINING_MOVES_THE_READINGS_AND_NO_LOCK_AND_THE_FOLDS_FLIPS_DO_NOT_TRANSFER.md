# The bank's learning path: training moves the readings and no lock, and the fold's flips do not transfer

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
runs (§3), each run once under the [pins](2026-09-29_THE_BANKS_LEARNING_PATH_PINNED_BEFORE_ITS_RUNS.md)
(`d84692dc`) at the build `6b9b1cee`; [proved-derived; formal-checked] for the Lean (§2);
[agent-inferred] where marked.

**What ran.** The bank's learning path: the covector of the receiving bank's lock, read at a
declared temperature, carried back to the source port `E` and deposited under the certified step
beside the linear readout's comparison; the members' pumps' covector read and held. The owners'
headers state it: `hnn::ring`, "The bank's face"; `hnn::prediction`, "The bank's learning path";
`hnn::constitution`, "The bank's learning path: a comparison beside the logits".

```sh
cargo run --release -p holonics --example hnn_prediction -- order2 learn
cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin <owner-only file> learn
```

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches four:
- **the helix**: the pump's clock and the resonance's doubled transport;
- **the cell holonomy**: the passage's monodromy, read at its second order;
- **faces and placement**: the lock's exchange face, the placement's rotations;
- **the pair**: every ordered pair of crossings.

The tube and the tower thread stay attached.

## 1. The lessons it answers

The pin's §0, each held:
- **1 and 2.** No class, lag or rule is computed by a routine; the bank is the declared one; every
  held-out request and the flips' probe are fresh draws of their own seeds.
- **5, an uncertified step.** `E` stepped by the certified step at every deposit (32 of 32 on
  order-2, 50 of 50 on text), the bank's own curvature, trust region and rounding charge in its
  certificate; every energy bound held; the pumps were held.
- **7, bits read as progress.** The face's and the readout's training codes stand beside the runs.
- **9, a larger limit.** No limit moved and each run ran once within its bound.
- **The seam lesson.** The covector is the lock's exchange face's own, `θ − q`; what it weighs is the
  passage's second order, whose ordering against the executed growth is the open item this run
  measures (§5).

## 2. The law and its Lean

The pin's §1–2 state it. The face: the kicked chart's transport `v = (2 + ihω)/(2 − ihω)`, member
`m`'s resonance amplitudes `W^±_m = Σ_t a_m² s_m^t ζ^(±t) z_t` (`ζ = v̄²`), the reading
`A = Σ_m p_m² (|W⁺_m|² + |W⁻_m|²)`, the face `θ_x = A(x)/Σ_y A(y)`, the loss
`log Σ_y A(y) − log A(t)` and its covector `θ − q` on the log-readings. The reading is quadratic
along a ray, `A(z + ηδ) = A(z) + η Σ Re(conj(K) W(δ)) + η² A(δ)`, and linear in each `p_m²`. The
certificate adds `C_bank = Σ (2Â₂/A₀ + (81/4) â₂/a₀)`, the trust scale `√(16 â₂/a₀)` and the rounding
charge `Σ 2e√(A₀ Â₂)`.

Lean `HNN/BankFace`, 12 theorems, `#print axioms` propext, Classical.choice and Quot.sound only:
`bank_face_covector`, `member_amplitude_ray`, `resonance_gain`, `log_one_add_ge`,
`bank_score_endpoint`, `bank_score_trust`, `rounded_alignment`, `sum_sqrt_mul_le`,
`joint_descends_beside`, `flip_reflection`, `flip_rotation`, `sideband_pair_sum`.

**Where the executed law departs from the kicked chart.** The executed tick is `A ⊗ 1 + pB ⊗ R(c)`,
its transport on the phase plane `(u, w)` and its reflection on the node plane; the node plane's
reflection conjugates `R(c)` to `R(c̄)` (`flip_reflection`), so the executed growth reads a passage
and its conjugate alike (the owner's test: one characteristic polynomial for member `m` on `z` and
member `−m` on `z̄`). The kicked chart's transport is conjugated to `Rot(v̄)` (`flip_rotation`) and
its traces differ. The executed pair terms `Re(c_t c̄_s) Re(β ζ^(t−s))` read the resonance and its
mirror equally (`sideband_pair_sum`): the face reads both. The executed transport is the lossy
`(24 + i√1023)/41`, its tick carries a self term in `p²|c|²`, and its pair kernel's lag-independent
part reads the member's own frequency `|Σ_t c_t|²`, the standing reading that past the bifurcation
boosts. On the spectral line the face orders the two quarter-turn neighbours equal and first and the
completing candidate first, as the executed growth does, and the line's own member below the
half-turn partner, where the executed growth orders it above.

## 3. The runs

**Acceptance 1, the exact checks: holds on both runs.**

| Run | Training: balances, pairings, commits, energy bounds | Unreached checks (loci) | The fold's lobes | The bank's locks: members certified, executed ticks closed |
|---|---|---|---|---|
| `order2 learn` | 512 of 512 each | 32 of 32 (224) | crossings at 31 of 32 deposits (1,576 slices), 57 halved, 5 dropped | 8,192 of 8,192; 491,520 of 491,520 |
| `text … learn` | 770 of 770 each | 50 of 50 (350) | crossings at 49 of 50 deposits (1,889 slices), 95 halved, 3 dropped | 255 of 255; 8,925 of 8,925 |

- The certified storage growth was 0 at every deposit (its product 1) on both runs.
- Every learned map stayed within the entry bound `8`: the largest entries were `R`'s `5057/4096` on order-2 and `2997/4096` on text.
- The order repair's generation closed 1,882 of 1,882 refinements' balances.

**The learning path, read on both runs.**

| Reading | `order2 learn` | `text … learn` |
|---|---|---|
| bank comparisons staged (skipped) | 2,244 (0) | 12,017 (0) |
| the face's top the target | 332 | 33 |
| the face's training code, `Σ −log₂ θ_t` | `5408 + 7/16 + ε` | `97771 + 12/16 + ε` |
| the flat face's code on the same comparisons | `2244 log₂ 5`, between 5,210 and 5,211 | `12017 log₂ 257`, between 96,203 and 96,204 |
| the readout's training code | `4035 + 13/16 + ε` (previous build `4020 + 7/16 + ε`) | `95160 + 5/16 + ε` (previous build `95129 + 1/16 + ε`) |
| `E`'s certified steps | `2^(−9)` to `2^(−6)`, 32 of 32 deposits moved `E` | `2^(−8)` to `2^(−1)`, 50 of 50 |
| `E`'s largest entry, from `1/2` | at most `1050621/2097152` | at most `66643/131072` |
| `E`'s certificate, first deposit | `a = 16903/2048`, `C = 37221/16` (the bank's `58067/64`), `c = 9989/2048`; step `2^(−9)` | `a = 51079/2048`, `C = 49965/64` (the bank's `62669/128`), `c = 61227/8192`; step `2^(−5)` |
| `E`'s certificate, last deposit | `a = 33771/65536`, `C = 31851/512` (the bank's `38441/32768`), `c = 30639/16384`; step `2^(−7)` | `a = 16575/4194304`, `C = 6073/1048576` (the bank's `4341/1048576`), `c = 33697/32768`; step `2^(−1)` |
| the pumps' covector (held), descent raising / lowering `p²` over the deposits | member 0: 28 / 4; member 1: 0 / 32; member 2: 27 / 5; member 3: 21 / 11 | the standing member: 19 / 31 |

At the first and the last deposit of both runs `E`'s step was set by its curvature, not by the
covector scale or the trust region.

**Acceptance 2, training reaches the bank: fails.** On the first 32 held-out requests the bank's
sections on the declared opening equal the trained constitution's on **256 of 256 stations**: **0
stations differ** (64 of 256 right on both).

**Acceptance 3, the order-2 terrain: fails its comparison.** 256 fresh requests, 2,048 held-out
stations.

| Reading | Released | Exact | Stations right | By station (of 256) |
|---|---|---|---|---|
| **the bank's locks** | 256 | 0 | **508** | 56, 62, 78, 60, 55, 55, 67, 75 |
| the order repair's linear readout, this run's constitution | 256 | 20 | 609 | 78, 76, 77, 73, 82, 72, 76, 75 |
| the linear readout on the previous build (the bank's receipt) | 255 | 21 | 638 | 82, 79, 81, 79, 83, 76, 81, 77 |
| the linear readout at its receipt (`af5e7de6`) | 249 | 39 | 866 | 112, 112, 111, 108, 108, 107, 108, 100 |
| the static marginal (class 0) | — | — | 512 | — |
| the per-station marginal | — | — | 520 | — |

- The bank reads 508 of 2,048: 4 below the static marginal, 12 below the per-station one, 101 below
  this build's readout, 358 below the readout's receipt.
- The bank's readings moved and none of its decisions did. The locked readings' growth ran from
  `33329/8192` to `138220` (the previous build: `33347/8192` to `138036`), and the least margin
  over a runner-up was `1585/4096` (previously `753/2048`). The stations right by station are
  identical to the previous build's, station for station.
- Every section was released at width zero: 2,048 refinements, one lock each; 46,080 turn
  readings.

**The regression: the fold's flips read on the held-out probe.** 31 lock proposals (1,005
half-turns), all 31 taken by the training code's exact comparison. On the 16 probe requests (seed
`2_026_092_905`, no run trains on or evaluates them), the turned sheets coded the probe **strictly
shorter at 15** and **strictly longer at 16**, none undecided. On text the lock took 46 of 49
proposals (1,323 of 1,377 half-turns); text has no held-out probe (every choosing pair is trained).

**Acceptance 4, text: fails.** The U6 choosing role's 385 pairs, two passes (`D = 35`, the bank its
standing member alone), then the 8 validation requests F0's rule selects:
- 7 sections released at width zero, of 32, 32, 32, 20, 31, 15 and 32 bytes before the
  termination, and 1 held (a typed refusal); none is UTF-8, and **the output is illegible**;
- 256 refinements, 1,085,568 turn readings, 255 locks certified (8,925 of 8,925 ticks closed), the
  locked readings' growth from `11547/512` to `65439/64`, the least margin over a runner-up
  `27/2048`.

The sections are owner-only and were shown in the conversation whole, with nothing beside them. By
count only, against the bank's receipt's sections (the readout's training alone, the previous
build):
- four sections changed (0 to 3);
- three are identical (4, 5, 7);
- one held where it released before (6);
- the two requests of 2,932 bytes gave identical sections again, and one small set of byte values
  recurs across all of them.

The training codes stand above, beside the run.

## 4. Time and memory

| Run | Measured | Projection | Peak resident bytes |
|---|---|---|---|
| `order2 learn`: training | 382,929 ms | 300,000–540,000 | |
| the order repair's generation | 84,397 ms | 60,000–150,000 | |
| the bank's generation | 1,074,616 ms | 900,000–1,400,000 | |
| the opening's diagnostic | 65,934 ms | 50,000–200,000 | |
| in all | 1,607,879 ms | bound 2,700,000 | 1,246,330,880 |
| `text … learn`: training | 957,586 ms | 600,000–1,000,000 | |
| the bank's 8 sections | 699,790 ms | 600,000–1,500,000 | |
| in all | 1,657,376 ms | bound 3,000,000 | 1,116,897,280 |

No run reached its bound or its internal stop; both runs are complete. On order-2 the training's
staging took 131,450 ms and its deposits 83,796; the lock's comparisons 79,343; the probe 79,680;
the bank's images and comparisons 24,237. On text: staging 385,530, deposits 431,939, the lock's
comparisons 133,094, the bank 168,806.

## 5. What the measurement located [agent-inferred]

- **Training reaches `E` and the readings; it reaches no decision** (the blocker, by its
  measurement: 0 of 256 stations differ from the opening's, and the by-station counts equal the
  previous build's).
  - Over 32 certified deposits `E`'s largest entry moved from `1/2` to at most
    `1050621/2097152`, by less than `2^(−10)`. The steps were `2^(−9)` to `2^(−6)` of the unit
    step, set by the curvature at the first and the last deposit. At the first the readout's part
    of `E`'s curvature was the larger (`37221/16` in all, the bank's `58067/64`).
  - The lock decides by the executed growth, and its least margin over a runner-up is `1585/4096`
    in growth. The moves shifted the locked readings (`33347/8192` to `33329/8192` at the low end,
    `138036` to `138220` at the high) and turned none.
  - On text the steps reached `2^(−1)` at the end: the certificate's curvature fell to `6073/1048576`
    as the returns' alignment fell to `16575/4194304`. Four of 8 sections changed and one is now
    held.
- **The face does not read the order-2 rule.**
  - Its training top is the target at 332 of 2,244 comparisons, below the 561 a symbol's share
    would give.
  - Its code over those comparisons (`5408 + 7/16 + ε`) is longer than the flat face's
    `2244 log₂ 5`; on text (`97771 + 12/16 + ε`) it is longer than `12017 log₂ 257`.
  - Each deposit descends the joint score on its own batch (the certificate); over the run the
    face codes the comparisons above flat. Its readings are set by the candidate's own image (the
    located cause named before the run, lesson 3), whose power does not depend on the request.
  - The second order weighs the rule's pair (the candidate and the cell two back) as one of the
    candidate's pairs with the 40 request cells and the locked stations, all at unit weight. The
    bank's receipt located that the rule is not a spectral line of the request, and a declared
    bank has no key naming the lag. A larger step would move `E` toward a face that does not read
    the rule.
- **The fold's flips decide on training code that does not transfer.**
  - The lock took 31 of 31 proposals on the training batch's exact comparison. On 16 requests
    no run reads, the turned sheets coded strictly shorter at 15 and strictly longer at 16.
  - The flip's decision carries no information about the admitted future: a coin, where the
    training code always wins. That the readout fell from 866 to 638, and to 609 on this build, is
    consistent with this; the probe reads each flip's sign, not the fall's cause.
  - **The law, from the retention and future-sufficiency laws.** Retention is a quotient
    sufficient for the admitted future, and a half-turn of a standing is a jump between two retained
    constitutions. The batch whose covectors proposed the jump selected it, so its code at both
    sheets measures that batch, not the future. **A jump of the retained constitution is decided by
    the lock's face on the declared future receiver:** the code of a probe of the passage, declared
    before the jump and read by no deposit, at both sheets, strictly (`θ > ½` on that receiver's
    weights). The proposing batch proposes and never decides. The probe is its own declared
    receiver, never the evaluation's material, so transfer stays graded on material no run reads
    (lesson 8).
- **The executed law against the kicked chart** (§2). The executed growth reads a passage and its
  conjugate alike, and the face reads both sidebands. The face's ordering agrees with the executed
  growth on the spectral line's top and its completion, and disagrees on the line's own member (its
  static boost).

## 6. Owed in #62

"The bank's learning path" (September 29):
1. **The executed law's full second order.** Derived on the executed Cayley tick: the self term in
   `p²|c|²`, the lag-independent part `|Σ_t c_t|²` (the standing reading), and the kernel's
   coefficients. The conjugation symmetry and the two sidebands are proved (`HNN/BankFace`).
2. **The growth against the face past the perturbative regime.** The ordering of candidates by the
   executed growth against their ordering by the face. They are measured to disagree on the
   spectral line's own member, and on order-2 no lock follows the trained readings.
3. **The members' pumps' step.** The bank as a locus of the constitution, and a certificate of the
   executed growth along a pump's own ray (the tube of monodromies; the reach record's item 2).
4. **The lock's temperature.** The exchange face over the candidates at a declared temperature as
   the pumped ring's basins under noise (the parametron record's interpretation, still owed).
5. **The fold's jump at the declared future receiver.** A half-turn decided by a declared probe's
   code at both sheets descends the admitted future's expected code: the probe's code as the future
   receiver's receipt, under the retention's future-sufficiency (`Foundation/Standing`).

## 7. The verdict

- **Acceptance 1 holds**: every balance, pairing, commit, energy bound, unreached-locus check,
  entry bound, lobe law, Floquet certificate and executed tick closed on both runs.
- **Acceptance 2 fails**: training reaches `E` and the bank's readings, and turns no lock (0
  of 256 stations differ from the opening's).
- **Acceptance 3 fails its comparison**: the bank reads 508 of 2,048 (marginals 512 and 520; the
  readout 609 on this build, 866 at its receipt).
- **Acceptance 4 fails**: 7 sections released and 1 held, none legible.
- **Built and exact**:
  - the covector of the lock's decision: the exchange face over the candidates, its readings the
    passage's second order at each member's resonance and its mirror;
  - carried back to `E` and deposited under the certified step, with its own proved curvature,
    trust region and rounding charge;
  - the pumps' covector read and held;
  - where the executed law departs from the kicked chart, proved (Lean `HNN/BankFace`, 12
    theorems).
- **The regression, measured**: the fold's flips decide on training code that does not transfer (15
  to 16 on a held-out probe), and the law is stated: a jump's comparison reads the declared future
  receiver.

## 8. Gates

- `cargo check --workspace --all-targets`: clean.
- `cargo test -p holonics --lib`: 956 passed, among them the learning path's:
  - `the_banks_transport_is_the_nodes_lossless_cayley_multiplier`;
  - `the_executed_turn_reads_a_passage_and_its_conjugate_alike`;
  - `the_banks_face_reads_a_spectral_line_and_its_completion`;
  - `the_banks_reading_is_quadratic_along_a_ray_and_its_covector_exact`;
  - `the_banks_images_are_its_placements_readings`;
  - `the_banks_returns_are_its_scores_differential_in_e`;
  - `the_banks_deposit_is_certified_and_its_score_falls`.
- `bash tools/lean_check.sh Holonics HolonicsResearch`: 10,250 jobs built, no `sorry`.
- The GPU suite: not run. No HNN behaviour on the card changed (the CUDA crate reads none of the
  changed items; the field's words are unchanged, and a deposit without the bank's reach is read
  exactly as before), and the worker's isolated worktree does not take the card's lock.
