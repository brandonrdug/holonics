# The bank's learning path, pinned before its runs

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the construction and the pins; [proved-derived; formal-checked] for the Lean
(§2); [measured] for the development reads (§4), which used development seeds and the text's
choosing role only.

**Occasion.** The [bank's receipt](2026-09-29_THE_BANK_READS_A_SUPERPOSED_PASSAGE_THE_LOCKS_CONTINUE_A_SPECTRAL_LINE_AND_THE_ORDER_TWO_TERRAIN_STAYS_AT_THE_MARGINAL.md)
measured its blocker: training reaches nothing the bank reads (256 of 256 stations equal on the
untrained opening); no covector of the lock's decision reaches `E` or a member's pump. This loop
builds that path: the covector of the lock's decision, carried back to `E` and to the members'
pumps, deposited under the certified step. It also measures the regression the bank's receipt
found in the linear readout (866 at its receipt, 638 on that build, the fold's lock taking 31 of 31
training flips).

## 0. The recorded failures this work could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **1, an authored routine.** Nothing names the order-2 rule, a lag or a class. The face is the
  parametron lock's own exchange face over the station's candidates; the readings are the passage's
  second order through the declared bank; the covector is the face's derivative. The bank is the
  parametron record's, unchanged.
- **2, recitation or an index.** The bank reads the receiving ring's storage, the moment's
  placement through `E`; the training reads the readout's partition of each request (the locked
  targets placed, the compared stations never their own target). No window, pair table or copier.
  The held-out requests and the flips' probe are fresh draws of their own seeds.
- **3, text as the exception.** One construction for every stream: storage through `E` at the
  residues, read by the bank's chart. The text run changes only the declared period (`D = 35`, the
  standing member alone).
- **4, the byte marginal / the section outweighing the request.** Named before the run as the
  expected blocker (lesson 3): the bank's receipt located that a lone candidate weighs one and a
  request cell one over the request's length, so a candidate's own image sets most of its reading;
  the face first learns what depends on the candidate alone.
- **5, an uncertified step.** `E` steps by the existing certified step, and the bank's comparison
  adds its own proved curvature (the quadratic reading's second order and the logarithm's), its
  trust region, and the charge of its covector's rounding to the alignment. The joint certificate,
  the storage certificate, the fold's lobes and the Floquet reach are unchanged. The members'
  pumps are held (§1).
- **7, bits read as progress.** The face's training code and the readout's are reported beside
  the runs, never as an acceptance. Text's sections are shown whole, in the conversation only.
- **9, a larger limit.** No law's limit moves (`s = ½`, `ηc ≤ 1`, the storage search, the entry
  bound `8`, the lobes, the reach). The learning runs' training stop is this pin's own, set from
  the development reads before any measured run (§3); no run is repeated with a larger bound.
- **11, the programming language.** The design is stated in residues, modes and spectral placement:
  each datum's image at its rotation, the passage's power at a member's parametric resonance and
  its mirror.
- **The seam lesson: the covector is the lock's own face.** The face is the lock's exchange face
  (`Objects/ParametronLock`, two sheets: `θ = a/(a + K)`) read over the candidates at a declared
  temperature; its covector `θ − q` is that face's derivative, not a surrogate beside it. The
  reading it weighs is the passage's second order, where the executed lock compares growths: the
  two agree on the known truth's top and completion (§2), and their ordering past the perturbative
  regime is owed (#62).

## 1. What is built (`6b9b1cee`)

`hnn::ring`'s header, "The bank's face"; `hnn::prediction`'s, "The bank's learning path";
`hnn::constitution`'s, "The bank's learning path: a comparison beside the logits".

- **The face** (`hnn::ring::{ReceivingBank::chart, BankChart, Resonance}`). The kicked chart's
  transport is the node's lossless Cayley multiplier `v = (2 + ihω)/(2 − ihω)` (`(3 + 4i)/5` for the
  declared bank). Member `m`'s resonance amplitudes over a turn are
  `W^±_m = Σ_t a_m² s_m^t ζ^(±t) z_t`, `ζ = v̄²`: the pair sum of the passage's second order at its
  parametric resonance, and its mirror. The reading is `A = Σ_m p_m² (|W⁺_m|² + |W⁻_m|²) ≤ κ²|z|²`,
  `κ² = 2dΣ_m p_m²`. The station's face is `θ_x = A(x)/Σ_y A(y)` over the candidates.
- **The comparison** (`hnn::prediction::{BankImages, stage_bank}`). On the readout's partition
  (`mask`), at every compared station every class placed with the locked targets over `ν̂(v + 1)`,
  generation's candidates. The loss is `ℓ = log θ_t⁻¹ = log Σ_y A(y) − log A(t)` (nats), and its
  covector on each reading is `∂ℓ/∂A(x) = 1/Σ_y A(y) − [x = t]/A(t)` (on `log A(x)`: `θ_x − q_x`).
  Every storage is a sum of images `Φ(P^r E e_x)`, read once per constitution.
- **The returns** (`bank_reach`, `deposit_with_bank`). The gradient on each reading,
  `K = 2ĉp²W`, is carried by the chart to the storage and back through each placement's rotation to
  `E`: one return per shared phase of each request, one per class over the batch. Each reading's
  covector is carried at its dyadic face (64 significant bits), so the returns' denominators are
  the readings' own powers of 2 and 5 rather than every station's normalizer's; the rounding is
  charged against the alignment.
- **The certificate** (`hnn::constitution::{BankReach, NormalLaw::prepare}`,
  `holon::deposition::JointReading::beside`). The returns join `E`'s window beside the readout's:
  they enter its metric, its unit step `D`, its alignment and its covector scale, not its feature
  moves. Along `D`, with `δ_x = δ + νP_j De_x` every candidate's exact storage move,
  `Â₂ = κ² Σ_x |δ_x|²` and `â₂ = κ²|δ_t|²`:

  ```text
  C_bank = Σ (2Â₂/A₀ + (81/4) â₂/a₀),   c_bank = max √(16 â₂/a₀),   a ← a − Σ 2e √(A₀ Â₂)
  η(s κ² b + C_bank) ≤ a,   η max(c, c_bank) ≤ 1,   s (Σ η m)² + η_E² C_bank ≤ Σ η a
  ```
- **The pumps are held.** The covector reaching a member's `p_m²` is
  `∂ℓ/∂(p_m²) = Σ_x c_x (|W⁺_m(x)|² + |W⁻_m(x)|²)`: read and reported, not deposited. The bank is no
  locus of the constitution (its members are the parametron record's declared bank), and by the
  certified step's existing law a pumped ring's own gains are held until a certificate covers the
  monodromy along their ray (#62, the reach record's item 2).
- **The flips' held-out probe.** At every lock proposal of the standing's fold, the same
  comparison's code is read at both sheets on 16 fresh order-2 requests (seed `2_026_092_905`,
  partitions `2_026_092_906`) that no run trains on or evaluates. It is a reading only and decides
  nothing.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects the loop touches four:
- **the helix**: the pump's clock `a² s^t` and the resonance's doubled transport `ζ^t`;
- **the cell holonomy**: the passage's monodromy, read at its second order;
- **faces and placement**: the lock's exchange face over the candidates, the placement's rotations;
- **the pair**: every ordered pair of crossings, carried by the transport between them.

The tube (the turn's `d` crossings) and the tower thread (the growth's dyadic enclosure, the
covector's dyadic face) stay attached.

## 2. The law and its Lean

Lean `HNN/BankFace` (12 theorems; `#print axioms` propext, Classical.choice and Quot.sound only):
- the face's covector, `d/dε (log Σ_y A_y e^(ε δ_y) − log(A_t e^(ε δ_t)))|₀ = Σ_y θ_y δ_y − δ_t`
  (`bank_face_covector`), the lock's `dθ = θ(1 − θ) d ln a` on every candidate
  (`Objects/ParametronLock.bias_susceptibility` is its two-sheet case);
- the reading along a ray, `|W + ηV|² = |W|² + 2η Re(W̄V) + η²|V|²` (`member_amplitude_ray`), and the
  chart's gain, `|Σ_(t<d) ω_t z_t|² ≤ d Σ|z_t|²` for unit carriers (`resonance_gain`);
- the score's endpoint bound: `log(1 + u) ≥ u − 2u²` for `u ≥ −1/2` (`log_one_add_ge`), so
  `Δℓ ≤ (A(η) − A₀)/A₀ − (a(η) − a₀)/a₀ + 2((a(η) − a₀)/a₀)²` where `a(η) ≥ a₀/2`
  (`bank_score_endpoint`), and the trust region `η²â₂ ≤ a₀/16` gives `u ≥ −1/2` and
  `2u² ≤ (81/8)η²â₂/a₀` (`bank_score_trust`);
- the rounding's charge (`rounded_alignment`, `sum_sqrt_mul_le`) and the joint certificate with a
  score beside the logits (`joint_descends_beside`);
- **where the executed law departs from the kicked chart.** The node plane's reflection conjugates
  a pump's reflection to its conjugate carrier's, `F R(c) F = R(c̄)`, and the kicked chart's
  transport to the conjugate turn, `F Rot(v) F = Rot(v̄)` (`flip_reflection`, `flip_rotation`). The
  executed tick is `A ⊗ 1 + pB ⊗ R(c)`: its transport acts on the phase plane `(u, w)`, so the
  executed growth reads a passage and its conjugate alike. The owner's test
  `the_executed_turn_reads_a_passage_and_its_conjugate_alike` checks this exactly: member `m` on `z`
  and member `−m` on `z̄` have one characteristic polynomial, and the kicked chart's traces differ.
  The executed pair terms `Re(c_t c̄_s) Re(β ζ^(t−s))` read the resonance and its mirror equally,
  `½ Re β (|Σ c_t ζ^t|² + |Σ c_t ζ̄^t|²)` (`sideband_pair_sum`), so the face reads both. Three
  departures stay:
  - the executed transport is the lossy `λ = (24 + i√1023)/41`
    (`4/3 − √1023/24 = 1/(24(32 + √1023))`, between `1/1536` and `1/1535` in tangent);
  - the executed tick carries a self term in `p²|c|²`;
  - its pair kernel has a part independent of the lag, which reads the member's own frequency
    `|Σ_t c_t|²`: the standing reading, which past the standing bifurcation boosts.

**Known truth** (the owner's test `the_banks_face_reads_a_spectral_line_and_its_completion`). On the
bank's spectral line, the face orders the two quarter-turn neighbours equal and highest, as the
executed growth does (`[1061/16, 531/8]` each). With the last cell open, the completing candidate
reads the face strictly first, as the executed lock's flip does. The face orders the line's own
member below the half-turn partner, where the executed growth orders it above (`[46, 1473/32]`
against the silent partner): the own member's static boost is not a second-order reading.

## 3. The pins

Every run runs once, on the host, in release, sequentially, at the build `6b9b1cee` or its pin
commit, each bounded externally at its projection's upper end.

**Acceptance 1: the exact checks.** Every training refinement's balance, pairing, commit and
committed energy bound; every unreached locus unchanged at every deposit; every learned map's
largest entry at most `8`; the fold's lobe law at every deposit; every lock of the bank's
generation certified on every member with every executed tick closed. **Passes** when every count
equals its total.

**Acceptance 2: training reaches the bank** (`hnn_prediction -- order2 learn`). On the first 32
held-out requests, the bank's sections on the declared opening (`Constitution::initial`) against
the trained constitution's: the count of differing stations of 256. **Passes** when it is positive.

**Acceptance 3: the order-2 terrain** (`order2 learn`: the bank pin's terrain and seeds, 512
training requests, 256 fresh held-out requests, `D = 60`). Reported:
- the bank's held-out stations of 2,048, against the static marginal's 512, the per-station
  marginal's 520, and the order repair's linear readout on this run's constitution and at its
  receipt's 866;
- the flips: the fold's proposals taken and refused by the training code, each read on the probe
  (strictly lower, strictly higher, undecided at the turned sheets).

**Passes** when the bank's stations exceed 520.

**Acceptance 4: text** (`hnn_prediction -- text <the U6 passage cut> <owner-only file> learn`). The
U6 split's choosing role, its 385 request relations, two passes; no `--read-reserve`; the evaluation
window never read. The 8 validation requests F0's rule selects (`RELEASE_SEED = 20_260_929`) are
generated by the bank's locks, their sections written whole to the owner-only file and shown in the
conversation only, with nothing beside them. Bits (the training codes) are reported beside the run,
never as its success.

**Acceptance 5: the projections** (from §4). A run that reaches its bound is reported incomplete
with its partial evidence and is not rerun with a larger bound.

| Run | Projection | Internal stop | External bound | Peak resident set |
|---|---|---|---|---|
| `order2 learn` | training 300,000–540,000 ms; the order repair's generation 60,000–150,000 ms; the bank's generation 900,000–1,400,000 ms; the opening's diagnostic 50,000–200,000 ms | training 1,200,000 ms; the bank 1,500,000 ms, read between chunks of 32 | 2,700,000 ms | about 1,200,000,000 bytes |
| `text … learn` | training 600,000–1,000,000 ms; the bank's 8 sections 600,000–1,500,000 ms | training 1,200,000 ms; the bank 1,500,000 ms, read between chunks of 4 | 3,000,000 ms | about 1,000,000,000 bytes |

## 4. The development reads

**Order-2** (`develop learn 64 32 16`: development seeds 21 and 22, the probe at seed 23; 64
training requests in 4 deposits, 32 evaluated):
- every check held (64 of 64 balances, pairings, commits and energy bounds; 4 of 4 unreached
  checks);
- 244 bank comparisons, none skipped; the face's top the target at 48;
- `E`'s certified step `2^(−9)` to `2^(−8)`, set by the curvature at both ends:
  - at the first deposit `a = 18567/2048`, `C = 20725/8` (of which the bank's `29347/32`),
    `c = 2533/512`;
  - at the last `a = 26151/16384`, `C = 7639/32` (the bank's `25775/1024`), `c = 42169/32768`;
- the pumps' covector: member 0's descent raised `p²` at 4 of 4 deposits, member 1's lowered it at
  4 of 4, members 2 and 3 split;
- the flips on the probe: 1 proposal taken, its turned sheets' probe code strictly higher; 2
  refused, both strictly higher;
- training 40,728 ms: staging 15,198, deposits 9,255, the lock's comparisons 7,605, the probe 7,607;
- the readout 109 of 256 held-out stations (the bank pin's development read: 109);
- the bank 63 of 256 (the same 63), in 136,366 ms;
- the bank on the declared opening equal to the trained one's on 256 of 256 stations;
- peak resident set 968,372,224 bytes; 252,674 ms in all.

**Text** (`develop learn-text`, the choosing role only):
- 32 pairs in 2 deposits: training 89,492 ms before the stations and the certificate's requests ran
  as co-present regions, and one deposit of 16 pairs after it 14,495 ms (staging 6,066, deposits
  8,293), with identical certificate readings;
- the certificate at the first deposit: `a = 51079/2048`, `C = 49965/64` (the bank's `62669/128`),
  `c = 61227/8192`, the step `2^(−5)`, set by the curvature;
- the bank's two development sections (choosing requests already read) in 176,443 ms, peak
  768,192,512 bytes.

The projections: order-2 training about eight times the development's (32 deposits, 31 of the
bank receipt's proposals, each lock and probe reading about 2,500 ms); text training 49 deposits at
about 15,000 ms; the generations as the bank's receipt measured them.

## 5. What is expected, named before the runs [agent-inferred]

- **The step is small against the lock's margins.** `E` steps by `2^(−9)` to `2^(−8)` of its unit
  step on order-2, bounded by the readout's curvature as much as the bank's; the bank's
  development locks lead their runners-up by at least `7879/4096` in growth. After 4 deposits no
  station changed. Over 32 deposits the count of differing stations is expected small, possibly
  zero.
- **The candidate's own image** (§0, 4) sets most of a candidate's reading, so the face learns
  first what depends on the candidate alone; the face's training top reads near the marginal (48 of
  244 at development).
- **The flips.** At development every flip read on the probe coded it longer at the turned sheets.
  If the pinned run repeats that, the lock's comparison on the training batch does not transfer,
  and the law is stated from the retention and future-sufficiency laws in the receipt.
