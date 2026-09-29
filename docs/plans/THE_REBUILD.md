# The rebuild

**Status: active, September 28.** Tracked in #63. This plan is the one order. The laws live in their
guides and owners; [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) is the position; the
[construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
keeps the history this plan replaced: steps 0–8, the step-4 design and its five campaigns, and the
forward plan F0–F6 as it stood.

## The unified plan (September 28)

[definition; agent-inferred] Brandon, September 28: "tie together all of our plans and designs and then
proceed with the necessary next items", so that the codebase does not become overgrown or frayed.
Three read-only audits of that day (plans and guides; Rust owners and consumers; Lean, atlas,
notebook, records and #62) located the fraying, and GPT-6 Astra reviewed the draft against them.
Its corrections are folded in.

### 1. One Holarchy, its laws, and what is not yet joined

- **The architecture** [interpretation]. The machine is one Holarchy ([THE_MACHINE](../THE_MACHINE.md)).
  Its receiving role is a population: the receiver mixes its constituent families by Bayes, the
  discrete replicator. The landmark tree is one family; a field-derived predictor (today the combined
  tree-and-wave face `q_C`) is another, read at the HNN's own port through its enclosure (U1's first
  loop); terrain navigators and composed eggs are others. This settles
  the containment the guides stated both ways (the population inside the field, the field inside the
  population): the population is the receiving composition at the field's port. It does **not**
  establish that the population or its statistical families are Holons joined at power ports; that
  join is open (§4).
- **The laws, each under its own hypotheses.**
  - Quadratic port dynamics obey `Holon/Deposition.learned_energy_balance`,
    `dE/dτ = −⟨e, Re⟩ + ⟨e, Le⟩ + ⟨e, Bu⟩ + ½⟨x, Q̇x⟩`, whose kinematic reading is the motion
    primitives (objects §3, `Geometry/Motion`) where `Q` is invertible and `R` symmetric. Singular
    storage and discrete junction scattering keep their own laws.
  - Statistical receivers obey their own update and code identities: the tree's counts (a node's
    split moves by `a′ − a = (y − a)/(N + 2)`), the population's telescope `∏_t q_t = Σ_f π_f L_f`,
    dormancy's fixed share over switching paths. They carry no stated energy, units or ports.
  - Deposition governs every reached change of constitution in both.
  - Their physical interconnection is an explicit construction obligation, not a consequence.
- **Retention** is the future-sufficient quotient (action-sufficient where the machine acts), taken
  at aeon boundaries (objects §8). The HNN's structural collapse releases learned material and cannot
  be reopened; species collapse keeps seeds and shares and can split. Each keeps its recoverability
  condition.
- **Release** is one decision law whose arms are the certified draw, the threshold commit, the probe
  and the typed refusal. The HNN's commit and the population's draws return its arms through
  `receiver::release` (U3's first loop). So do the chaser's certified capture and its probe (U3's
  second loop). Its cornering commit is a declared separate arm, whose separating term is the price
  of a tick.
- **Charts.** Text, arithmetic, motion and image are boundary charts of the one machine. Brandon,
  September 28: the physical computation is the ideal, and framing the machine as text prediction
  makes the problem harder. The construction proceeds from the motion. Text is one chart, and its
  product, Athena-0, keeps its independent acceptance (the gates below).

### 2. What exists, read against it

| Part | State |
|---|---|
| Landmark tree | earns: standing cut `3 + 1/16 + ε` a cell held out; unseen agent text about `1 + 12/16` bits a byte |
| Population | codes known-truth terrain at its truth among declared families; the egg alone is F0's byte predictor; no library owner calls it (the harnesses do) |
| Field (rings, contacts, word, deposition, wave) | lawful on host and card; `5 − 13/16 − ε` held-out bits on the standing cut through `q_C`; campaign 2 and the loaded resonator added none; its wave and resonator states live inside one word |
| Chase (F6) | reception at truth on 16 arenas; action captures in 164 ticks against 3,704 and 366; the at-once acceptance failed; each tick is released through the one law (the certified capture, the probe) or the declared cornering arm, and F6's action law is amended to that rule (U3's second loop) |
| Retention | one contract (objects §8): each collapse is the standing law through its own carrier, with its Lean standing and its recoverability (U2's first loop); the test-only linear chain is retired |
| Release | one law, `receiver::release`: the HNN's threshold commit and the population's certified draws, stop law and refusals (U3's first loop); the chaser's certified capture and probe (U3's second loop), its cornering commit a declared separate arm priced by the tick |
| Mixtures | four constructions, sharing the ideal telescope but differing in conditioning, transitions and carriers: digit-local joins (`JoinTree`, `FaceJoins`), the population's telescope with death (over families carrying their faces, `Population`, or read at a port, `PortPopulation`, which is the HNN's receiving face since U1 retired the whole-cell `receiving::Mixture`), dormancy's fixed share over switching paths, and the retired `LocalMixture` |
| Motion primitives | proved in `Geometry/Motion`; no Rust consumer |

### 3. The order

Each item fixes its owners, its consumer equation, its acceptance and its failure branch before it is
measured, and keeps every inherited gate below verbatim.

#### U0. Consolidate (no new law) — carried out September 28

Its receipt is in [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md#u0-receipt-september-28) and on #63.

The deliverable is a smaller, consistent tree. Acceptance: each retirement names the owner that keeps
its law, or writes the law into its guide or record first; nothing live consumes what is retired;
every duplicated law has one owner that the others cite; the gates pass (check, tests, Lean, atlas).
- **Rust.** Retire, with exports, tests, registrations and atlas rows in the same commit:
  `population::local` and `hnn_population_local` (its executed floor's switching bound is recorded
  first); `hnn_tokens`; `hnn::born` and `hnn_born` (Lean `HNN/BornFace` stays); F1's
  `population::{words, sectioned_words}`, `terrain::words` and `hnn_word_probe`;
  `Mixture::switching`; `navigator::reflection`; `holon::reaction`, `landmark::identity` and
  `landmark::primitive` with `aeon::zeta`, each after its unformalized argument is written down;
  `landmark::constraint`; `exponentiated::transport`; the CUDA word path's unused wrappers; the
  completed drivers `hnn_diagnose`, `hnn_lattice_growth`, `hnn_curated`, `hnn_terrain`,
  `hnn_release_terrain` (its checks kept as law fixtures). Their library dependencies stay: the crib
  helpers and `grain_logits` feed live paths. `hnn_population` stays, with its live routes. Rename the
  half-turn (`swing` → `half_turn`), junction scattering (`junction_swing` → `junction_scattering`),
  the chase's `Policy` and `Constitution`, `Founding.epoch` and the "sign generator".
- **Lean.** One owner, cited by the rest, for the half-turn word law, the sling, the moving-metric
  energy law, Bayes and KT; the junction's declarations renamed; retired-crate docstrings repinned;
  `TARGETS_FORMAL_CATALOG.md` retired.
- **Guides and indexes.** One owner per definition; the operator contract gains the population and
  the terrain; the old Swing wording goes; stale status sections are rewritten; this plan replaces the
  old order, and the construction record keeps the history; the measurement protocol and the guards
  move to THE_MACHINE; #62 becomes the current obligation list; the atlas README states its tags and
  shards; the notebook and records READMEs become routes.
- **Kept, with an actual consumer or a date.** `receiver::standing`, `compression::face_map` and
  `hnn::modes` (a test-only chain; U2 retired all three, below) and `receiver::release`'s unconsumed half and `causal_chord` (U3
  retired it at its second loop, below) are kept until U2 and U3 close, and each item's acceptance includes it: at the item's close each kept
  subtree has a named call from a library owner or is deleted. `physics::fluid`'s control-volume
  operators (`control_volume::{NewtonianMaterial, ControlVolume, face_flux, vorticity}` over
  `cells::{GridCell, CubicalComplex}`) are kept for U4's fluid-cell terrain; the rest of `physics`
  meets the same rule at U4's close.

#### U2. One retention contract, and F0's memory

Owners: Lean `Foundation/Standing` (its Rust chart `receiver::standing` retired in the first loop),
`hnn::retention`, `population::species`, `compression::landmark::context`.
- **Contract.** Both collapses share the abstract factorization law (`standingLaw_exists_iff_future_factors`)
  with action-sufficient futures, through their own carriers: the HNN's structural collapse keeps its
  refusal to reopen; species collapse keeps seeds, shares and its certified future. No dense global
  representation is forced on either.
- **F0's memory experiment, early** (the measured product obstruction: 2,653 bytes of standing a cell
  read). Merge the tree's contexts where the decoding and continuation squares hold under every
  admitted action and deposit, not merely where present faces or validation code agree; then measure
  the storage.
- **Acceptance.** The collapses' laws and tests unchanged; on a fresh F0 split, pinned before running
  with its standing budget, the merged tree's standing per cell falls strictly while its conditional
  byte-and-stop code stays within the pinned margin of the unmerged tree's. The squares are checked, or
  the merge is refused for that context. `receiver::standing`, `compression::face_map` and `hnn::modes`
  each have a named call from a library owner, or are deleted.
- **Failure.** The standing stays; the refused contexts and their separators are reported.
- **First loop, September 28 (the contract, the derivation and a census; nothing adopted).**
  - *The contract* is in [objects §8](../ELEMENTARY_OBJECTS.md#the-retention-contract), which owns
    it; the owners cite it. Its Lean standings: `HNN/Retention.fieldStanding` (the structural
    collapse, which cannot be reopened), `Context/Evolution.species_collapse_standing` (new: the
    species retention `(t, W)` is a standing for every cell word within the certified future; it
    splits by `species_split`), and the tree's chains (`Context/Standing.address_standing`,
    `Compaction.compacted_is_the_full_tree`). Hearing's consumer at the collapses is
    `hnn::retention::separator`, which refuses at the aeon's close every pending ratio whose
    receiver still hears a released locus.
  - *The kept subtree, retired.* `receiver::standing` and `compression::face_map` are a dense
    linear chart of the standing law and of the face map's kernel; no collapse is linear, and the
    contract certifies each through its own carrier, so none needs them. `hnn::modes` quotients a
    loaded ring's word-local state, which leaves at every word's end, so an aeon's collapse has
    nothing of it to act on. Their laws are Lean's (`Foundation/Standing`, `Compression/Core/FaceMap`,
    `HNN/ModeQuotient`); the two only `hnn::modes` checked are in
    [HNN_FORMULA §4](../HNN_FORMULA.md#the-loaded-rings-mode-quotient). All three are at commit
    `1bdacc8f`. §4's campaign-3 row now waits on persistent motion between words.
  - *Which merges are future-sufficient* (derived in `compression::landmark::context`, "Which merges
    and releases are future-sufficient"; Lean `Context/Merge.equal_present_faces_do_not_merge`).
    For the declared receiver, the exact node merges are the chains already stored and the contexts
    no continuing address reaches; equal present faces, equal counts and equal validation code do
    not qualify. The exact merges are therefore essentially empty, and **the memory experiment's
    acceptance is amended accordingly**: it tests the charged coarsening law
    (`Context/Merge.coarsening_within_margin_iff`), a declared coarser receiver priced by its
    code-length pair, with its own acceptance and never reported as retention. The squares clause
    applies to exact merges, which the derivation already refuses beyond the chains.
  - *The census* (`hnn_population f0-census`; the egg alone on F4's development passage; 107,150 ms
    at an 8,656,285,696-byte peak). Of the egg's 2,653 bytes a cell its byte tree holds 2,651: the
    readings kept beside the state (certificates, cached stop weight, rebase count) 1,140, the
    boundary contexts 0 (10,184 bytes in all), letters no label reads 3; once-reached leaf chains
    1,771; the depth cut at 12 ticks 594, at 6 ticks 1,984; the refused equal-count merge of
    siblings 827. The table is in the tree's owner.
  - *The acceptance run pins, before it runs:* a fresh development-family split never used for a
    diagnostic; the declared receiver (the conditional byte-and-stop code at `L_R = 16`); the
    candidates (the unmerged tree, once-reached chains released at the aeon boundary, the depth cut
    at 12 ticks), chosen on the choosing families alone and charged `⌈log₂⌉` of the candidates; the
    margin `m` in bits and the standing budget in bytes a cell; and the readings beside the state
    reported as their own line (standing only for a receiver that reads the certified residual).
  - **Acceptance run, September 28: passed; the depth cut at 12 ticks adopted**
    ([record](../../research/records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md);
    pins `d6feae7e`, run `d31c8b37`, `hnn_population u2-acceptance`). A fresh split (seed
    `holonics-u2-development-families-2026-09-28-v1`), `m = 1214` bits (half F0's gain over flat),
    the budget 1,298 bytes a cell. The choosing families chose the depth cut (`+96 + 0/16 + ε`
    charged against the unmerged tree); the once-reached chains released at each conversation's
    opening cost `+18693 + 8/16 + ε` and were not admissible (retired). On validation the cut coded
    `+224 + 12/16 + ε` above the unmerged tree, charged, within `m`, and the standing fell from
    2,651 to 2,049 bytes a cell (1,134 without the readings, within the budget; 2,049 whole, past
    it). 262,138 ms at an 8,620,863,488-byte peak. F0's egg now declares its byte tree at 12 ticks.

#### U3. One release contract

Owners: `receiver::release`, `population::{releasing, text_release, provenance}`,
`population::chaser`.
- **Contract.** Every emission is a `ReleaseReturn` of one decision law; its arms are the certified
  draw (the inverse CDF), the threshold commit, the probe and the typed refusal. `P_release = P_scored`
  is kept, and so are the stop law, the unresolved draw mass and the refusals. The chaser's rule is
  declared as what it is, a capture-basin commit with an information probe; the specified sequential
  test on accumulated log-odds is either built as its own arm or the F6 law is amended to the built
  rule, explicitly.
- **Acceptance.** Every existing receipt is reproduced exactly through the one law: the face laws, the
  stop law, the unresolved draw mass, the refusals and the full receipts of F4's views and the chase.
  The inverse-CDF theorem does not turn selectively emitted mass into the full mixture, so no claim
  rests on it. `receiver::release`'s unconsumed half and `causal_chord` each have a named call from a
  library owner, or are deleted.
- **Failure.** A receipt that the one law cannot reproduce names its separating term; that rule
  stays a separate arm, declared as such.
- **First loop: the contract at exact parity** (September 28, done). `receiver::release` owns the
  one decision law and states it; its arms are the threshold commit (`Released`, `Widen`), the
  certified draw (`Drawn`), the probe (`Ask`) and the typed refusals (`Hold`, `Unresolved`,
  `NoContinuationBridges`). The draw is the law at tolerance zero on the key's class reading (Lean
  `Population.{certified_draw_is_released_at_zero_tolerance, plural_draw_is_held}`); the key is the
  separating term, so a width law that returns a draw is refused. `population::sampling` and
  `family_release` moved into it (`draw`, `draw_exact`, `Population::select_family`), and the
  harness's two response loops became the library's `Population::release_response` (scored and
  ancestral laws, the stop law, per-cell family provenance). Parity: the pre-U3 selectors and
  harness loops, run beside the law, agreed on 20,000 interval faces, 20,000 exact faces and 1,600
  responses (every status, bytes, family, face count, posterior width and scored trace). The kept
  subtree: the zonotope, the compatible families, the probe searches and the coarsening tower had no
  consumer and were retired, their laws in Lean or in
  [RECEIVER_HOLARCHY](../RECEIVER_HOLARCHY.md#width-and-release); the Rust `ReleaseCoarser` arm
  went with them. `population::health` was retired (its bound is in the same section; the draw holds
  on a simplex-covering face); `population::provenance` is called by the scored response.
  `causal_chord` is not a release owner (a decision reads widths, never a transfer object); its one
  consumer is `hnn::modes`'s check of `hnn.mode-quotient-chord-survives`, which has no Lean
  counterpart, so its disposition joins `hnn::modes`'s at U2. (U2 retired `hnn::modes`; the second
  loop, below, retired `causal_chord`.)
- **Second loop: the chaser's arm at exact parity** (September 28, done).
  - *The arms.* `MachineChaser` decides each tick through `release`, with `DecisionRule(Release,
    Ask)` at tolerance zero on the capture-within-`m` reading over the selected fibre. The basin's
    certificate over every member is width zero, and the law returns `Released`, the certified
    capture. Beyond it the law returns `Ask` with the offered probe, or `Hold` where none is offered.
  - *The probe's partition.* The probe carries its `ProbePartition`: its class sizes against the
    commit's, constructed only where it separates the fibre strictly more (`∏|c|^|c|` strictly
    smaller; Lean `Population.partitionInformation_lt_iff`). Its criterion is information; the
    retired residual-width fields of `ObservationProbe` went.
  - *The cornering arm.* The cornering commit (`MachineRelease::Commit`) takes the law's `Hold`, or
    an `Ask` whose concession exceeds `d·|Θ|`. It is the Bellman stop law's one-step comparison,
    declared separate, and the price is its separating term.
  - *Parity.* The harness, built before and after, agrees line for line with the wall times
    masked: the reception's 414 lines, `action trace`'s 342, and `choose 2 12 0`'s 150 / 4,668 /
    240. `action trace` adds 12 lines, one for each uncertified release. A scratch printer agreed
    tick by tick on 64 machine passages (the acceptance seeds at `d = 0, 1, 256`, the choosing seeds
    at `d = 0`). The pre-U3 selector agrees on 8,320 fixtures in `chaser_tests.rs`. Of the 164
    acceptance releases, 152 are `Released` and 1 is `Ask`, on seed 20260942 (`2^64·3^18` against
    the commit's `2^60·3^24`). Eleven are cornering commits: 10 beside `Hold`, and 1 priced out on
    20260932 (a concession of 242 above the price 0). The receipt is in the notebook README.
  - *F6's law is amended* to the built rule, by that parity (F6 below: the superseded text, the date
    and the reason). The specified test's statistic is identically zero inside the fibre, and 143 of
    the 152 certified releases came over a plural fibre, where the test would still be sampling.
  - *The kept subtree closes.* `receiver::release`'s probe arm now has its library call (the chaser's
    `Ask`). `receiver::causal_chord` had no library caller once `hnn::modes` retired, so it is
    retired, its module and its tests, 2,801 lines (history at `c10acca9`). Its laws are Lean
    `Foundation/CausalChord` (the transfer object, poles ⊆ eigenvalues, the rebase, the rate form and
    the seam, the Jordan counterexample, the spectrum's insufficiency), `Foundation/ReceiverAtlas`
    (the full probe atlas separates) and `Transport/HolonicInteraction` (the port storage rate). The
    laws only the Rust carried are in
    [RECEIVER_HOLARCHY](../RECEIVER_HOLARCHY.md#the-causal-chord): the Faddeev–LeVerrier construction
    and its coefficientwise certificate, cancellation, poles named by their factors, residues, the
    resolvent's index, and the six-vertex cospectral pair. `ratio::polynomial` keeps the half-plane
    count and the rational-root census as the one owner of the pole readings. They now have no
    library caller and are public readings of the exact arithmetic, and their agreement with
    Sylvester's inertia is tested at the owner. The partial-fraction `extended_monic_gcd`, which only
    the residues called, went with the chord.
- **Then** F4's second stage, `Q_R` (its gate below).

#### U1. One machine: the receiving composition at the field's port

Owners: `hnn::receiving`, `hnn::reference`, `receiver::population`, `compression::landmark::context`.
It consumes U2's and U3's contracts.
- **Consumer equation.** The HNN's receiving face is the population's face over the two families it
  already weighs, the tree and the combined face `q_C` (tree grain logits plus the wave), with matched
  priors, the same per-cell prequential order (deposits inside a receiving window included), one
  authoritative tree update, and the existing combined-face covector, phase comparison and
  window-level wave deposition. `q_C` lives in `ℚ(θ)`, so the family contract carries an algebraic
  face or an enclosure, or a declared rational chart with its residual. Zero likelihood stays exact
  death, never a positive floor.
- **Acceptance.** First, exact identities on small fixtures between `receiving::Mixture` and the
  population on the declared families. Then, on the standing cut, the two executions' codes differ by
  at most a bound derived from their charts (β rounding against the enclosures), pinned before the
  run, host and card. Aggregate agreement alone is not acceptance.
- **The missing physical maps, named.** U1 states what joining the statistical families to the
  Holon's power ports would need (their flow and effort, the storage their counts or weights would
  be, and the balance their update would satisfy) and lands the obligations in #62; it does not
  claim the join.
- **Then F2's adoption gate, unchanged:** a field family is adopted for text only if the charged
  population code is strictly shorter than without it and its complete work fits the declared
  response and passage budgets (the gate below).
- **Failure.** The separating term is named, and the two mixtures stay, recorded.
- **First loop, September 28: the pins** (committed before any standing-cut run; Refs #73 #63).
  - *The owner.* `receiver::population::port::PortPopulation`, the population at a port: the
    families' faces are the machine's readings, so it carries only the priors and each family's
    likelihood, and reads its face, weights, code and deaths through `Population`'s own telescope
    and outward bounds (one helper, `weigh`). *The family contract* is an enclosure: a face in
    `ℚ(θ)` enters as its exact enclosure `[lo, hi]` (a point where rational), the likelihood is
    carried between the endpoints' products, and zero is exact death (Lean
    `Population.population_mixture_enclosed`). The receiver's population
    (`hnn::receiving::receiving_population`) holds the tree `T` and the combined face `C` at one
    bit each, `π = ½/½`, and receives each phase's two faces in cell order, deposits inside a
    window included (`ReceivingStep`); the tree's one update stays the constitution's landmark
    deposit, and the covector, the phase comparison and the wave's deposition are untouched.
  - *The consumer equation.* The population's face `q^P_t(x) = (L_T q_T(x) + L_C q_C(x))/(L_T + L_C)`
    is `two_face_prior` at `π = ½`. The mixture's executed face is `(β̂_t q_T + q_C)/(1 + β̂_t)`, with
    `β̂_(t+1) = β̂_t q_T(x_t)/(q_C(x_t) ρ_t)` and `ρ_t = lo_t/(q_C(x_t)(1 − r_t))` (the chart and the
    rebase), so `β̂_t = β_t/∏_(s<t) ρ_s`.
  - *The bound, derived and proved* (Lean `Population.{executed_face_within_population,
    executed_mixture_within_population}`, over `two_face_skew` and `execRatio_eq`): at every cell
    `|log₂ q̂_t(x_t) − log₂ q^P_t(x_t)| ≤ |Σ_(s<t) log₂ ρ_s| ≤ D_t`, and over the passage
    `|log₂ ∏_t q̂_t − log₂(½ L_T + ½ L_C)| ≤ Σ_t |log₂ ρ_t| ≤ D_n`, where `D_t` is the mixture's
    certified drift before cell `t`: `Σ_(s<t) ⌈(hi_s − lo_s)/lo_s · 3/2⌉_(2^(−128))` plus `3·2^(−W)`
    a rebase. Enclosures containing the true codes are then at most `D_t` apart.
  - *The acceptance, pinned for the standing cut, host and card* (`hnn_exposure`, both executions on
    the same faces in the same compare, `hnn::reference::Agreement` at `19f1eb61`): (i) at every scored phase the
    two code enclosures lie within distance `D_t`; (ii) the mixture's summed code and the
    population's telescope `−log₂(½ L_T + ½ L_C)` lie within `D_n`; (iii) the population's summed
    per-cell codes meet its own telescope. Campaign 1's receipt sets the scale, not the pin:
    `D_n = 5844186179759863429570124736444603/2^126` bits at `W = 28` with 6,147 rebases.
  - *The fixture identities* (`the_receivers_population_is_the_mixture_cell_by_cell` at
    `19f1eb61`, whose population half stays as
    `the_receivers_population_weighs_by_likelihood_cell_by_cell`; `receiver::population::port_tests`). On dyadic faces that fit the carrier, `β = 1, 3, 5/3, 7/9`,
    the two executions give the same exact weight of the tree (`1/2, 3/4, 5/8, 7/16`), the same exact
    face of the received class (`1/2, 3/8, 5/8`) and the same product (`15/128 = ½ L_T + ½ L_C`), and
    each code encloses the same exact code length. At an exactly zero combined face the
    population's family dies, with weight exactly zero and the tree's exactly one; the carried ratio
    has no death and refuses the step. The population at a port equals `Population` over families
    carrying the same faces, enclosure for enclosure.
  - *Projection.* Campaign 1's standing-cut exposure took 399,911 ms on the host and 353,499 ms on
    the card. The population adds one code and one receipt over two families per phase. The public
    control's first 512 windows took 38,514 ms at a 332,091,392-byte peak. Each run is projected
    within ten minutes and within 4 GiB, and is stopped past that.
- **First loop, September 28: the standing cut, passed; the mixture retired** (runs at the pins'
  commit `19f1eb61`, `hnn_exposure cut-file … cells all`; the cut's SHA-256 is
  `5c5613d3b0df5fe6fb8f7fca3c33cfcf90f99b65bcb3ccda0cfb29d39f23df4f`, 6,148 cells, 3,074 windows,
  1,190 held out; only counts and bits are reported).
  - *Host.* Complete, every window deposited. Every one of the 6,148 scored phases lies within its
    pin. The largest distance between the two code enclosures was
    `4003627267671666862783/2^97` bits, against that phase's pin
    `434487243236789459311460070663947/2^126`; the largest pin read was
    `5843235441867343318430037831758637/2^127`. Over the passage, the mixture's summed code and the
    population's telescope lie `99019428869303789749073/2^96` bits apart, against the final drift
    `2922093089908766130445036760152251/2^126` (`W = 29`, 6,147 rebases). The population's summed
    per-cell code meets its telescope, at distance zero. Held out, both read `3671 + 9/16 + ε` bits,
    `3 + 1/16 + ε` a cell (campaign 1's reading), with population − model in
    `[158292311810566627/2^92, 2643712553560870977/2^96]` bits. On the training cells the difference
    is in `[1547136580660878604245/2^90, 99016940284749758855251/2^96]`. The run took 367,066 ms at a
    400,457,728-byte peak.
  - *Card* (`realization card`, alone on the idle RTX 4080 SUPER under the GPU lock). The run was
    complete and PASSED. Its readout equals the host's line for line outside the wall times and the
    traffic (3,332 lines compared): the same pins, distances, drifts and codes. It took 318,378 ms at
    a 498,278,400-byte host peak, with 444 MiB on the card.
  - *The retirement* (the one owner, agent-inferred from the acceptance's end state: the duplicate
    law goes, not an alias). The HNN's receiving face is now `hnn::receiving::score` over the
    receiver's population, which the constitution holds at the receiving locus. `Mixture`, its `β`
    chart, the rebase, the chart residual, the drift and `MixtureReport` are deleted, and so are
    the comparison's scaffolding (`Agreement`, the `population` and `drift` readings). Their law is
    in Lean: `Tree.{execRatio, execMix, sequential_mixture_executed}` and the bound
    `Population.executed_{face,mixture}_within_population`. The course's `log₂ β` is now the
    population's log-odds `log₂(L_T/L_C)`. `L_model` lies within one bit of the better face with
    no drift term (`the_receiving_face_codes_within_one_bit_of_the_better_face`).
    Standing-cut runs at the retirement's commit show the exposure's model reading the pins'
    population codes exactly, endpoint for endpoint: training
    `[715031979768513993871184210076879/2^95, 1430063959537028186828544322961367/2^96]` bits, held
    out `[145446044393744509099079416007333/2^95, 145446044393744564611838278662333/2^95]`. Host and
    card agree line for line outside the wall times and the traffic, and every verdict against the
    baselines is unchanged. The constitution's curve drops the retired `β`'s bits at the receiving
    locus. The host took 359,998 ms at a 374,853,632-byte peak; the card took 308,234 ms at a
    499,388,416-byte host peak.
  - *The missing physical maps, named* (objects guide, "The receiving storage"; owed in #62). For
    the population: storage `Φ(ℓ) = ln Σ π e^ℓ`, flow the per-cell `ln P_f(x_t)`, effort the
    posterior `∇Φ = w`, and the balance `ΔΦ = ⟨w, f⟩ + D(w ‖ w′)`, a Bregman remainder. For the
    tree: storage the log KT mass, flow the unit count, effort the face's log, and a lossless
    telescope. For the joint: a stated constitutive map from bits to port variables, a Dirac
    structure from the receiving ring's port to `ln q_C` (the softmax is not power-neutral), and a
    common clock (U5). The join is not claimed.

#### U4. Motion running

Owners: a Rust motion owner in `geometry` (the move pair `(v, v′)` over `ℚ(i)`, its kind and its pivot
where one exists), `holarchy::terrain::{chase, pursuit}`, then the named operators of `physics::fluid`.
- **The rebase** (with U1, independent of it). The chase carries `(v, v′)` undivided; its traction law
  `|v′ − v|² ≤ r²` reads as the disk of admitted moves; walls, speed caps, traction, demand timing and
  held slips are preserved; a zero opening velocity and a stop are explicit cases with no division and
  no pivot. Acceptance: every chase receipt is unchanged. Failure: a receipt that changes names the
  case the rebase broke, and the lattice kinematics stay as they are.
- **The measured next failure first.** The machine misses the truth-only least on 5 of 16 seeds while
  its opening fibre is wide; that is the next loop's subject, before any new terrain.
- **Next loop: the failure located, the expected plan, a fresh population** (September 28, done;
  receipts in the notebook README, `hnn_chase {diagnose, fresh, moves}`).
  - *The separator.* Each of the 5 misses enters at one tick. On four, the robust certificate ties
    across the moves (or certifies none within `m = 12`), and the tie goes to the fibre-summed tube or
    nearness. The worst case over the fibre does not read the members it does not bind. On the fifth,
    the truth's class parts only on the runner's cell of that tick, which is read after the move.
  - *The candidate* (`Plan::Expected`, `pursuit::expected_ticks`) reads every member at its posterior
    weight: the members an adaptive strategy leaves uncaptured within `m`, then the sum of the others'
    capture ticks. It was chosen on the choosing seeds (147 against the robust 150).
  - *The fresh population*, pinned before the run (62 chased seeds of `20261101 + s`, `s < 64`; two
    draws open within capture and are refused by the terrain): capture ticks 574 against the robust
    machine's 594, regret 9 against 29, and 12 won, 49 tied, 1 lost against it. The candidate
    improves on the current machine. Against both controls at once both machines pass F6's capture
    bullet there (37 and 35 of 62); on the 16 acceptance seeds that bullet's failure (7 of 16)
    stands. The switches are not built, so F6's action acceptance is not passed.
  - *The move set.* Pure boosts change no seed's truth-only least. The lattice realizes speed 1 along
    an axis against the declared `3/2`, and the half lattice lowers the least from 153 to 133 on the
    acceptance seeds and from 565 to 478 on the fresh ones: capture distance is a function of the top
    speed realized on each ray.
  - *Not adopted as the default.* Under the expected plan a `Released` capture certifies the
    terrain's strategy, not the machine's own continuation, since the plan may leave it
    (`receiver::population::chaser` at commit `7f2c5d4f`, "What `Released` certifies under each plan"). The expected plan
    becomes `MachineChaser::new` when its release reads its own continuation. Owed in Lean (#62): the
    expected recursion is exact, and a finer grain never raises the least capture. (The pledge,
    below, makes the release its own.)
- **The pledge: the expected plan's release is its own continuation** (September 28; receipts in the
  notebook README, `hnn_chase {choose, fresh}`).
  - *The law.* A `Released` tick carries its bound `B_t`, and the machine keeps the pledge
    `T = min_t (t + B_t)`. Under the pledged expected plan `B_t` is the expected recursion's own worst
    case `W(u*)` (`pursuit::ExpectedCapture` gains it as a third coordinate, still exact), and once a
    pledge stands `E` is read to it, the horizon frozen at the release. The class the runner's cell
    names reads `U = 0` at the next tick's frozen depth, so each later `W′ ≤ W − 1` and every member is
    captured by `T` (`receiver::population::chaser`, "What `Released` certifies: the pledge"). The
    robust plans release `b(u*)` and keep it as before. The commit's certificate as the expected
    plan's bound and `W` read with a sliding horizon are not promises the plan keeps; on the 94 seeds
    read, the unpledged plan kept all 814 of its bounds, by the terrain.
  - *Chosen on the choosing seeds only* (the pinned rule): robust 150 capture ticks (3 won against
    both controls), certified-then-expected 148 (4), pledged expected 147 (4), each keeping every
    bound it released (144, 142, 141) and breaking no pledge. The candidate is the pledged plan.
  - *Pinned before the run*: the fresh population `20261201 + s`, `s < 64`, disjoint from every range
    read so far; the first fresh run's criteria (aggregate capture ticks, regret to the truth-only
    least, win/tie/loss against both controls at once, the candidate against the robust machine,
    F6's capture bullet as written); refused draws printed and entering no sum. The adoption rule:
    the candidate becomes `MachineChaser::new` exactly when its aggregate is strictly fewer than the
    robust machine's and it wins more seeds against it than it loses.
  - *The run* (once; 63 chased seeds, one draw refused): the candidate sums 618 capture ticks
    against the robust machine's 617 (regret 26 against 25), and wins 6, ties 54 and loses 3 against
    it. **The adoption rule is not passed**; `MachineChaser::new` stays the robust plan, and `action
    trace` on the 16 acceptance seeds is unchanged (164 capture ticks, 7 of 16 won against both
    controls at once: F6's capture bullet still fails there). Every released bound was kept (581 and
    582 ticks), no pledge broken. Against both controls at once the robust machine wins 28 of 63 and
    the candidate 32, so on this population F6's capture bullet passes for the candidate alone.
  - *The failure, by its measurement* (the next loop's subject): at an uncertified tick the expected
    order (fewest members uncaptured within `m`, then the tick sum) loses 11 ticks on one seed
    (20261203: 13 against the robust plan's 2, the truth-only least 2; neither machine certified
    over the fibre of 40 at tick 0), more than it gains elsewhere (12 ticks on 6 seeds, less 1 on
    each of two others). Owed in Lean (#62): the three-coordinate recursion is exact, and the pledged
    plan keeps its bound.
- **Known-truth game terrains** (Brandon, September 28;
  [record](../../research/records/2026-09-28_THE_OPTIMAL_POLICY_IS_THE_GEODESIC_NAVIGATOR_THE_CHASE_IS_RETROGRADE_ANALYSIS_AND_A_TEMPO_IS_A_MOBIUS_LOOP.md)),
  after the chase's next loop and before the fluid-cell terrain: the two-by-two cube's Cayley graph
  and king-and-queen and king-and-rook against king by retrograde analysis (the chase's capture basin).
  Each measures a navigator's charged description length against its regret to the optimal policy, with
  the table itself as the index control. The chase's next loop also records its capture distances as a
  function of the admitted move set.
- **F6's switches and attribution** follow U2 and U3 (they touch the action-sufficient future and the
  release law). Done September 28: F6's switch bullet passes as written on its pinned population
  (F6, "The switches and their attribution, built and read once").
- **F6's action acceptance stays as written, and its failure stays visible.** The next measurement
  is on a fresh, unfiltered population of seeds with its aggregate capture, regret and win/tie/loss
  criteria declared before the run. The subset of seeds that admit a win beyond every control is
  reported separately, as a conditional reading, never as the acceptance.
- **Then** a fluid-cell terrain from `physics::fluid`'s control-volume operators (the pressure as the
  incompressibility grip, doing no work; viscosity as friction on the strain; time advance and the
  pressure solve, which `physics::fluid` still owes), then the motor chart (its gate below).

#### U5. Clocks are aeons

A receiving window is an `aeon::Epochs` reading, a pump period an `aeon::Cycle`, and the machine's
clocks instantiate `navigator::Clock`. Acceptance: the section and carry correspondence is proved or
checked exactly, and every exposure is at parity. Failure: the clock that does not correspond is
named, and the program's loop stays its own counter, disclosed as such.
- **First loop, September 28: the clocks joined; every clock corresponds** (Refs #73 #63). The
  computational object is the helical pair interaction; the loop touches the helix (a clock is a
  circle plus carry), the tube (the receiving window as a clocked span) and the cell holonomy (a
  pump's cycle closes on its torus), with the pair, faces and placement, and the tower thread
  attached. Each choice is agent-inferred in its owner.
  - *The inventory and its dispositions.*

    | Clock (host and card) | Section, carry, period | Disposition |
    |---|---|---|
    | Ring `g`'s rotor clock, the lift coordinate `λ_g` | section `d_g ∣ λ`; its jumps are the carry into ring `g + 1`; period `d_g` | `navigator::Clock` (`hnn::field::Ring::clock_at`): the lift point's phase class and winding, the selective step's carry, the keys' crib opening and carried key, the cut's branch and the letters' register all read it; a signed coordinate (the map powers of `Ring::rotate`, a ring's point) splits by `aeon::Reading`, which agrees with the clock wherever both read |
    | The carry chain and the joint clock's carry-out | ring `g`'s carry on a cell is its section's flux over the cell's aeon | `aeon::Epochs` flux, proved (Lean `HNN/Moment.SelectiveDecl.carryIn_is_section_flux`); the carry-out stays the `aeon::Cycle` of the last ring's clock at the boundary (`hnn::retention::aeon_readings`). A ring's carry word is its section's epoch reading at the cell clock's sections: the carry word's runtime consumer (§4) is the selective step |
    | A ring's epoch ticks over a passage | the ring section's flux, `(r + N)/d` | `aeon::epochs` at `ClockLift::ring_section`, read by `aeon_readings` |
    | The receiving window | the cut's cell clock (an unwound `navigator::Clock`, one tick a cell) at the section `A ∣ x`, `A` the aperture | `aeon::Epochs`: window `k` is epoch `k`, `[kA, min((k + 1)A, n))`, the closed windows the flux `⌊n/A⌋` (`hnn::receiving::ReceivingPhases::windows`, which the exposure's loop reads; Lean `Aeon/Clock/Epoch.{forward_epoch_is_window, mem_epoch_digitTicks, odometer_tower}`) |
    | The word's clock (junction steps; the receiver's `e_0 … e_last`; the diamond's rounds and windows) | unwound, every tick on its section | `navigator::Clock::unwound` (already); the receiving epochs are its ticks, the epochs of the word's aeon at its unit section, disclosed as such |
    | The pump's clock | one circle of the step's order `1`, `2` or `4` | `aeon::Cycle` (`hnn::ring::PumpDeclaration::{clock, phase_at, period}`; the resonator's phase is the clock's torus point; Lean `HNN/Ring.pump_period_is_cycle`) |
    | A locus's deposit clock `m` | the locus's section, crossed by each deposit that moves it | `aeon::Epochs` flux, kept as its count (the constitution's header, unchanged: deposits only advance, so the count is the flux and its sufficient statistic) |
    | The keys' `steps_g(k)` and crib ticks | ring `g`'s clock over the crib | the ring clock's reading, its lift displacement (Lean `Winding.reading_navigatorClock`), summed from the selective step |
    | The moment's cells and an aeon's `cells` | the cell clock | the unwound cell clock's reading, which `receiving_windows` lifts |
    | The card's moment ingest carry and pump phase | device realizations | the ring clock's jumps (`before + step ≥ period`) and the pump clock's torus point (`t mod order`), each at parity with the host by the GPU suite and the card exposure |
    | The chase's switch clock | the tick clock at the switch cells | `aeon::Epochs` already (F6); untouched |
    | The exposure's compares, deposits and open windows, its deadline in windows, `Constitution::commit` | none | the program's own counters, disclosed as such (`hnn::reference::Exposure`) |
  - *Joins and deletions.* `hnn::field::phase_winding` (a copy of the division with remainder) is
    deleted: its readers go through `Ring::clock_at` or `aeon::Reading`. `hnn::ring::RingClock`
    (a micro-step walk counting section arrivals, test-only) is deleted: its law is read through
    `aeon::epochs` (history at `e5eb7304`). The letters' register keeps each ring's
    `navigator::Clock` instead of a copy of its arithmetic. `aeon::Epochs::intervals` gives an
    aeon's epochs as intervals (Lean `epoch_contiguous`). The exposure's stride `position += A` is
    replaced by the epochs of the cut's cell clock. The atlas gains `hnn.ring-clock`,
    `hnn.carry-is-section-flux`, `hnn.receiving-window-epoch` and `parametron.pump-period-cycle`, and
    `parametron.crossings-epoch-ticks` names the aeon owners.
  - *Lean.* `Aeon/Clock/Epoch.mem_epoch_digitTicks` (epoch `k` of a digit clock of base `n` is the
    window `[n k, n (k + 1))`) and `Aeon/Clock/Epoch.{forwardWord, forwardWord_chained,
    crossingTicks_forwardWord, forward_epoch_is_window}` (the forward walk `0 → n` of one clock is an
    aeon whose ticks at the section of grain `A` are the digit clock's, so its epochs are the
    windows: the Rust `receiving_windows` exactly); `HNN/Moment.SelectiveDecl.carryIn_is_section_flux` (the carry is the
    ring clock's jumps and the signed crossing count of its section over any aeon of its circle
    lift across the cell); `HNN/Ring.{pumpOrder, quarterTurn_pow_eq_one_iff, pump_period_is_cycle}`
    (`s = i^k` returns exactly at multiples of its order, `a² s^t = a² s^(t mod order)`, and an aeon
    of the pump's clock closes exactly when the carrier returns). Every correspondence of the item
    is proved; the loop leaves #62 no new obligation.
  - *Parity* (the standing cut, SHA-256 `5c5613d3…f23df4f`, 6,148 cells, 3,074 windows; only
    counts, bits and hashes). The host exposure before the loop (`e5eb7304`) and after it agree line
    for line outside the wall times (3,335 lines each; the 3,307 lines outside the setup line and
    the wall-time table hash alike): complete, 3,074 windows compared and deposited, held out
    `3671 + 9/16 + ε` bits, `3 + 1/16 + ε` a cell. Before, 391,605 ms at a 427,786,240-byte peak;
    after, 371,468 ms at a 383,205,376-byte peak (projected from the first, within ten minutes and
    4 GiB). The card (`realization card`, alone on the idle RTX 4080 SUPER under the GPU lock):
    complete, and its readout equals the host's before and after line for line outside the setup,
    realization, wall-time and bus lines (the 3,306 lines hash alike across the three runs); 331,710
    ms at a 483,717,120-byte host peak. The GPU suite: 32 passed. The loaded resonator's
    development pilot (`windows 32 resonator source`, the pump's phase read through its clock)
    agrees line for line outside the wall times (149 lines, stopped
    at its deadline at cell 64 in both). The chase's `action trace` agrees line for line with the
    wall times masked (354 lines; capture ticks 164 / 3,704 / 366); the switch clock is untouched.
  - *Verdict.* Every clock corresponds; none is left a counter but the program's own, disclosed.

#### U6. The text chart

- **Redirected September 29: the text chart is the one machine's field**
  ([record](../../research/records/2026-09-29_THE_TEXT_CHART_IS_THE_ONE_MACHINES_FIELD_TORI_HELICES_EGGS_AND_TUBES_ARE_ONE_FAMILY.md)).
  The byte-tree text line below (F0, F4, U2, and U6 items 1 and 2) broke HNN_FORMULA's laws: it
  coded bytes, addressed a window of the last `D` bytes and drew one byte at a time. It stops: no
  further tuning of, or comparison against, the context tree. Tori, helices, eggs, tubes, fractals,
  friction, knots and the flux physics are one family, and text enters the one machine's field as
  moments on its helices and leaves as a jointly refined section. The next loop is two owners,
  built in parallel: `hnn::encoding` (`E` founded by closing the receiving forms under the field's
  transports, no window) and `hnn::prediction` (a latent section refined by `K` words with the
  field's motion continuing, read jointly, released at width zero). Acceptance: exact balances,
  exact `T(x)` on copy and moiré terrain, then generated text sections shown whole. The data
  protocol (item 1) and the arithmetic contract (item 3) stay.

F0's next loop is U2's memory experiment; F4's second stage follows U3; F5 follows F0 and F4. The
curated source gains its intervals (source contract item 9), measured as a charged comparison
against the source without them. Their gates below are unchanged. Failure: each gate's own failure
branch; intervals that do not shorten the charged code are recorded and not adopted.

- **Audited September 29; restated**
  ([record](../../research/records/2026-09-29_THE_TEXT_CHART_AUDITED_ONE_PREDICTOR_SEEN_CONVERSATIONS_AND_NO_ARITHMETIC.md)).
  F0's acceptance run failed, and two independent audits of the chart found its method naive. The
  failures:
  - The comparison was lopsided: under full accounting the "egg" codes the curated stream
    `+2122 + 14/16 + ε` bits worse than the flat tree.
  - "Unseen families" were unseen messages inside conversations already read.
  - The "response stops" are mostly record splits and conversation switches.
  - The stream interleaves conversations with no per-conversation state.
  - The chart has no arithmetic.
  - Its generation is byte-by-byte sampling, not egg packing.
  - "Truth" named the logged reply, which is observed conduct; the name is retired.

  The chart's next loop is the record's §4, each item with its acceptance fixed there:
  - (1) the data protocol: conversations as the split unit, a reserve that nothing has read, and a
    state per conversation;
  - (3) arithmetic joined through one shared contract, in bases 2, 10 and 16, with producers of one
    face kept distinguishable.

  The symmetric comparison (2), generation as a requested consequence (4) and retention around the
  admitted actions (5) follow. F0's release gate, F4's curated release and F5 wait on them.
- **Item 1, the data protocol, built September 29** (`f68100f2`, `f4479d9d`; the
  [notebook's receipt](../../research/notebook/hnn_design/README.md#u6-the-data-protocol-by-conversation-with-a-reserve-nothing-reads-september-29);
  Refs #73 #148 #63). No passage was run; the split's checks are count-only, on metadata.
  - *The split by conversation* (`development_families.py U6`): the unit is the conversation, joined
    through its relations (one relation joins two of the 87). Choosing holds 61 conversations and
    16,314 messages, validation 11 and 682, the reserve 15 and 5,453. No conversation lies in two
    roles, and no relation crosses roles. Validation drew small conversations.
  - *The reserve* [agent-inferred]: 15 conversations, the least number whose mean reads no less
    sharply than validation's at one in five of the rest (`72·71 = 5112 ≤ 4·1290 = 5160`), leaving
    72 to choosing and validation. It is named
    `09d7ae5b86d1b34cd1f57a100fb0ec412f59902f6ec3b90924a7c80b136f8a24` in the scripts and
    `exterior.rs`. Every script refuses its material, and every artifact written before it was named,
    unless the logged `--read-reserve` is passed; no run passed it. Its conversations were read by
    the earlier splits, so it guards the choices made from now on.
  - *State per conversation*: the typed byte tree, the letter tree and the flat control keep one
    address per aeon, with their counts shared (`enter_aeon`; atlas
    `receiver.population-aeon-address`). A test reads two interleaved conversations context for
    context as each alone. This is not the reverted per-port trees of `38b0b81c`, which split the
    counts.
  - *The leaks*: the general future branch is the present branch. Retention holds each aeon's latest
    run on each target port and reads only the present (`receiver.population-present-retention`); on
    the choosing incidence it releases 7 of 12,261 requests. The flat control's release draws the
    egg's cap, never the logged reply's length. The invariance test: two passages that differ in a
    withheld continuation's bytes, length and future relations have the same request-time state,
    face, readout and keyed release, and the former future branch fails it.
  - *Wording*: "truth" no longer names a logged reply in the plan, the notebook or the harnesses.
  - `f0-acceptance` enters the aeons; the spent harnesses (`curated`, `f4`, `u2-acceptance`,
    `f0-census`, the F5 native paths) read one aeon and refuse every spent cut.
- **Item (3) derived, September 29**
  ([record](../../research/records/2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md),
  Lean `HolonicsResearch/Mathematics/ArithmeticContract`). The record states:
  - the arithmetic contract, its consumer equation and its provenance;
  - its code lengths;
  - its composition at a numeral port;
  - the build loop's acceptance (A1–A3, bases 2, 10 and 16, prose, Rust and Lean streams) and the
    smallest build that tests it.

  Its composition into the text chart's population reads item (1)'s protocol, built above.
- **Item 2, the symmetric comparison, September 29: holds**
  ([record](../../research/records/2026-09-29_U6_THE_SYMMETRIC_COMPARISON_PINNED_BEFORE_ITS_VALIDATION_ROLE_IS_READ.md);
  the owner `46267d56`, the pins `9b849f54`, the streams and projection `4e346d4e`; Refs #73 #148
  #63; only counts, bits and hashes).
  - *The comparison*: the candidate (F0's admitted egg) and the control (the context tree over every
    byte and letter, no slots, `D = 48`: `SectionSlots::Cells`, atlas
    `hnn.landmark-section-address`) read the same 268-symbol stream, each conversation's context its
    own. Every choice is charged to its side: the candidate its request pointer, the sweep's 17 bits,
    F0's 5 and the learned partition's description; the control its 3. The margin is F0's recorded
    range of the spent draws, `m = 534` bits [agent-inferred].
  - *The passage*: item 1's split at F0's aperture, 1,048,021 cells (`c6e51a35…ca2d4e`, validation
    524,009 cells in 11 conversations: 523,404 bytes and 605 letters). Its letters are 52 responses'
    ends, 214 record boundaries, 329 turns, no switch and 10 openings.
  - *The code, charged*: the candidate `1023189 + 2/16 + ε`, the control `1027201 + 2/16 + ε`, the
    difference `−4013 + 15/16 + ε`, below `−534`. **The acceptance holds.** [primary's note] Its scale:
    both sides code near `1 + 15/16` bits a byte, and the gain is under one bit in 128 cells. Its
    reach: the 11 conversations are unread by this run's choosing role, but F0's choosing role read
    all 87 development conversations and the candidate's settings were swept on material holding
    them, so this is a within-development measurement; only the evaluation partition (F5's) and
    conversations newer than the capture are unread by every run. The terms:
    - bytes `−3560 + 8/16 + ε` (agent `−3144 + 14/16 + ε`, human `−417 + 10/16 + ε`);
    - letters `−793 + 15/16 + ε`: record boundaries `−310 + 11/16 + ε`, turns `−560 + 13/16 + ε`,
      a response's end `+55 + 6/16 + ε` (its end `+147 + 5/16 + ε`), openings `+21 + 0/16 + ε`;
    - the pointer `+280 + 12/16 + ε`;
    - the charges `+58 + 11/16 + ε`.

    Uncharged, the candidate is shorter on 10 of the 11 conversations.
  - *Beside it*: the whole state is 2,099 bytes a cell for the candidate and 1,441 for the control,
    **both past 1,298**. The validation readings took 52,611 and 15,693 ms, the peak resident set
    was 7,223,922,688 bytes, and the run took 255,104 ms. The longest complete warm responses were
    29,182 and 8,288 ms.
  - *The releases*: 8 per side, each stopping at its own letter. The candidate stopped 6 and reached
    the cap on 2; the control stopped 6, reached the cap on 1 and stopped on 1 text-codec separator.
    Word tokens in the choosing vocabulary: 276 of 338 against 513 of 629 (the logged replies 1,118
    of 1,214). Both recombine vocabulary, and neither answers.
  - *What stays open*, measured: both states past the budget; the hazard at a response's end; the
    releases. Items 3–5 carry them, and F0's release gate, F4's curated release and F5 wait on them.
- **Item (3) built and its acceptance passed, September 29** (`c17ea7bd`, pinned in `54925b4c`
  before its draws were read; the
  [record's §8](../../research/records/2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md#8-the-build-and-its-acceptance-run-september-29);
  Refs #73 #148 #63).
  - *Built*:
    - `holarchy::terrain::arithmetic::Expressions`: the prose, Rust and Lean layouts in one declared
      glyph set, each line with its exact truth;
    - `receiver::population::arithmetic::{ExpressionPort, ExpressionEgg}`: the numeral port with no
      chart branch, the `^` pairing located by which results hold, the holds sheet over the byte
      tree, a receipt per expression, and the release as egg packing by certified draws;
    - the `arithmetic` mode of `hnn_population`;
    - Lean `jet_separates_across_keys`.
  - *The run*, seed `2026092903`, `2^10` expressions a base and chart, 105886 ms and 614312 kB
    against 240 s and 1 GiB projected:
    - A1: on all nine streams, under the located key, `A + B ≥ P(holds)` exactly on every
      expression, so the result cells cost at most `2N − log₂ C(2N, N) = 5 + 13/16 + ε` bits a
      stream. The egg's own code is within that plus the pairing's one bit, and the square and its
      rebase held on all 9216 expressions.
    - A2: every shared face (`a ^ 1 = a · 1`; sums whose operands share no bit, `a + c = a ⊕ c`) has
      its receipt naming the carried producer. On the faces-only control every other family died by
      the third face on all 192 runs.
    - A3: 1024 of 1024 reached on every stream, and the contract's code was equal on every equal
      expression across the charts. The keystone's value against the byte tree alone lies between
      `20262 + 13/16` and `23610 + 12/16` bits a stream.
    - The failure branch: no pinned expression unreached. The declared forms outside the layouts
      (`(2 : ℕ)`, `2u64`, `1_000`, `1,000`, `0o17`, `-`, words, chains, `2 ^ 70`) are recorded
      unreached. The port's numeral start was revised for every chart during development, before
      the pin, after it misread `1,000 + 1 = 1,001`.
  - *Disclosed*: the byte tree's 16-byte context cannot tell an operand's end from a result's in
    prose and Rust (`1469 + 8/16 + ε` bits on 1024 ends in prose base 2, against `22 + 4/16 + ε` in
    Lean). Its composition joins the native field (`hnn::encoding`, `hnn::prediction`, the redirect
    above), not the byte tree.

#### U7. The targets, alongside

Every existing target obligation stays (RH, Hodge, complex Euler and Navier–Stokes, BSD, their Lean
and #62). The motion primitives add these, each graded and each with its Lean piece:
- Navier–Stokes as free fall on the volume-preserving rearrangements (Arnold), the pressure as a
  workless grip, viscosity as friction on the strain alone (frame indifference); helicity conserved
  without friction; vortex stretching as the strain boosting the vorticity (Beale–Kato–Majda);
- phase volume changing only through the boost's trace;
- purity, for RH and Hodge: the boost pinned by the weight, the turn free (Deligne's torus);
- the de Bruijn–Newman flow: de Bruijn's strip law `y² ≤ Δ² − 2t` for polynomials, the barrier's
  winding as conservation of faces across a surface;
- Turing's method as the clocked turn (ticks on the line against the total winding); Sturm and
  Prüfer shooting as the leap.

#### U8. Hardware and curation

F3's gate (below) when the product deadline needs the card; parity for every change to the existing
resident HNN made by U1, U3 or U5 (the GPU suite, alone on an idle card); Lean curation (#147);
equation extraction (#146).

### 4. The open joins and the learner's necessities, each disposed

| Item | Disposition |
|---|---|
| The tree and population as Holons joined at power ports | open; U1's first loop named its missing maps and balances ([objects, "The receiving storage"](../ELEMENTARY_OBJECTS.md#the-receiving-storage)); owed in #62 |
| Campaign 3's descended lattice chart, card parity, finite-deposit stability, persistent dormancy across an aeon and the concrete-ring bridge | U2 retired `hnn::modes` (its state is word-local); these return with persistent motion between words (below), the mode quotient ported from `1bdacc8f` with that consumer (#73); the Lean parts owed in #62 |
| Mode release, FOUND by interconnection, far-field moment quotient `V_m` | deferred to after U3 (#73) |
| Encoding, Context and JointPrediction (joint against marginal witnesses) | U6, after U1; the continuation-transport discovery of [F1's after-note](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#f1-the-word-alphabet-campaign-5-73-148) stays live |
| Concrete-tick diamond, complete word-sensitivity certificate | owed in #62 |
| The carry word's runtime consumer, relative completeness, action-sufficient descent in Lean, Hearing's consumer | the carry word's consumer is the selective step, whose carry is a ring's section flux cell by cell (U5, Lean `HNN/Moment.SelectiveDecl.carryIn_is_section_flux`); Hearing's consumer is `hnn::retention::separator` at the aeon's close (U2); owed in #62 (relative completeness, action-sufficient descent) |
| F4's decoder, producing keys, causal provenance, grain and fibre, release squares | U3 and F4's gate |
| F5's cold restore, atomic native transition, truthful health receipts | F5's gate |
| Moving-continuum electromagnetic reception | deferred to U7 (the physical terrains); owed in #62 |
| Persistent motion of the wave and resonator between words | open: the word-local states leave at the word's end; built only with a consumer and a falsifier |
| Timing and intervals | U6 (source item 9), charged |
| Calibration (predicted against realized surprise) | U3's receipts report it |
| Gain by precision, and the hazard ladder | U2 (deposition step by reading precision) and U1 (the switch rate), each with its acceptance before adoption |
| Regeneration from the quotient | kept as the identity that regenerated passages add no evidence in expectation; no training on them |
| The ring-search experiment (rings as the search for keys, not as predictors) | restored: after U1, on the moiré and rotor terrains, it measures search work against enumeration and menu propagation, and basin mass against a declared prior, with a nonlocking control ([learner record §2](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#2-the-rings-as-the-search)); residual-founded transport discovery first ([§14.1](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#141-birth)). The founding law is built and proved (`receiver::population::birth`, Lean `Context/Birth`; [record](../../research/records/2026-09-28_RESIDUAL_FOUNDED_TRANSPORT_DISCOVERY_PINNED_BEFORE_ITS_SEEDS_ARE_READ.md)). Its acceptance failed as pinned: on six of eight parity-moiré seeds the declared families did not fail, so nothing was founded. On the two that founded, the newborn coded at the truth. The founding closes observability only: its dimension exceeds the emission's Hankel rank by the forms silent on the reached orbit (a conserved charge on two seeds), so the minimal realization also needs the reachable quotient. The next loop is a terrain whose declared families do fail, with the reachable quotient; if it fails again, the Rust owner is retired and the law stays in Lean. **The rings as the search, measured September 28** (pinned, then run once; [record](../../research/records/2026-09-28_THE_RINGS_AS_A_SEARCH_FOR_KEYS_PINNED_BEFORE_THE_RUN.md)): neither the search nor the prior holds. The pumped ring bank misses seeds on both moirés, and on the crib it spends `5640 rem 64405 over 268218` times menu propagation's work. Its unpumped control proposes as well as it does, and undriven it lands on a plural lock in all but `[596/2^24, 597/2^24)` of its configurations. The rings are not a search, and `hnn::keys`'s menu propagation remains the key search. The driver and harness are retired (history at `10a837fd`) |
| The F6 law's threshold commit against the built planner | U3's second loop: F6's action law amended to the built rule, the sequential test's statistic being identically zero inside the fibre (F6) |

### 5. The waves

- **Wave A:** U0, three workers on disjoint paths (Rust; Lean, atlas and #62; guides and indexes),
  with this plan written by the primary.
- **Wave B:** U2's contract and F0's memory experiment; U3's contract; U4's rebase (disjoint).
- **Wave C:** U1, consuming U2 and U3; then F2's gate and the ring-search experiment; U4's next loop.
- **Wave D:** U5 and U6; U8's parity with each change to the resident HNN; U7 alongside every wave.

### 6. The former labels

| Former | Now |
|---|---|
| Steps 0–3 | complete (construction record) |
| Step 4 (the HNN law), campaigns 1–2 | built; U1–U5 join it |
| Campaign 3 (modes, dormancy, founding) | U2 retired `hnn::modes`; the rest in §4 |
| Campaign 4 (the motor chart), F6 | U4 |
| Campaign 5 (encoding, context, prediction) | U6; §4 |
| F1 (words) | its failure branch holds: bytes stay; the continuation-transport discovery of [F1's after-note](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#f1-the-word-alphabet-campaign-5-73-148) stays live (§4) |
| F2 (the field as a family) | U1 and its gate |
| Step 5, F3 | U8 and its gate |
| Step 6 | U7 |
| Step 7 | U0, U8 |
| Step 8, F4, F5 | U3, U6 and their gates |
| F0 | U2's memory experiment, U6 and its gate |

## The gates (inherited verbatim)

[definition] The product and terrain gates of the forward plan of September 27, kept word for word:
the U-items above consume them and change none, except F6's action law, which U3's second loop
amended explicitly (F6 quotes the superseded text). Owners their receipts name that U0 retired
(`LocalMixture`, `hnn_tokens`, F1's word family, `hnn::born`, `Mixture::switching`) are at commit
`2d34b819`. Their receipts are in the records they cite and in
the [construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md).

### F0. The predictor on unseen families (the release's gate; #73, #148)

[definition; agent-inferred; [audit and diagnosis](../../research/records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md)]

**The diagnosis** (the first loop, done September 28, re-reading F4's development passage by
component). On unseen families the population codes the bytes `−2430 + 8/16 + ε` bits below the flat
tree, half its gain on the choosing families. F4's whole-stream `+1346 + 1/16 + ε` is the cost of the
section letters and the request pointer, which the flat stream never codes. The rate on unseen agent
text is about `1 + 12/16` bits a byte, a PPM-class rate: its releases carry real words (580 of 758
word tokens) and are not yet legible. The standing is 10,983 bytes a cell. The posterior sits wholly
on the admitted egg, and the trees beyond depth 24 add at most 20 bits.

- **Builds on.** `receiver::population` with its dormancy and fixed share,
  `compression::landmark::context`, the merges, `Context/Merge.merge_cost_mass_iff`, the hazard ladder
  and continuation transports ([Astra's review](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#146-gain)),
  and the family-split scripts.
- **The comparison.** Like with like. The code of the bytes (and of each response's stop, which a
  release must predict), given the observed sections, is read against the flat tree on the same
  bytes. Section letters that a conversation supplies are observed, not predicted, so they are not
  charged to either side. Whole-stream codes stay reported.
- **Candidates**, each adopted by the choosing families alone:
  1. **Drop what carries no share. Adopted September 28.** On the choosing families the posterior
     sits on the admitted egg, so the population becomes the egg alone (`hnn_population f0-egg`).
     - Validation bytes are unchanged, `−2430 + 8/16 + ε` against flat, and choosing bytes
       improve by 2 bits, since no family names are paid.
     - The standing falls from 11,513,530,863 to 2,781,355,912 bytes (from 10,983 to 2,653 a cell).
     - Peak resident memory falls from 10,843,217,920 to 3,400,306,688 bytes, and the passage from 272,849 to
       166,113 ms.
  2. **A family wins where it is closest: measured, not adopted, September 28**
     ([record](../../research/records/2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md#5-the-population-a-family-wins-where-it-is-closest);
     [receipt](../../research/notebook/hnn_design/README.md#f0-candidate-2-a-family-wins-where-it-is-closest-september-28)).
     `receiver::population::LocalMixture` keeps each member's posterior at each gating context,
     the last `d` cells (node-local Bayes; Lean `Population.{local_telescope, local_mixture_code,
     local_of_constant}`). Its executed chart holds a member at `2^(−64)` of its context's leader,
     which also makes it return at `64 + log₂ M` bits (`hnn_population f0-local`, the eight
     declared families).
     - The choosing role chose `d = 0` from `{0, 1, 2}`, charged 2 bits. On the choosing stream the
       rung `d = 0` read `−247 + 0/16 + ε` against `d = 1` and `−259 + 0/16 + ε` against `d = 2`.
       The gating ladder in space is not adopted.
     - Validation bytes read `−2727 + 1/16 + ε` against flat. Against the egg alone they read
       `−298 + 8/16 + ε`, and `−296 + 8/16 + ε` with the 2 bits charged. The choosing bytes agree,
       charged, at `−3 + 12/16 + ε`.
     - The gain is dormancy in time. Over the whole passage the mixture codes `254 + 14/16 + ε`
       bits below its best single member, which no static mixture can do; exact whole-passage
       Bayes over the same families reads as the egg alone.
     - The standing returns to 10,983 bytes a cell (11,513,530,846 bytes), from 2,653. The passage
       takes 263,687 ms at an 8,407,535,616-byte peak, and streaming the standing raises the peak to 14,226,153,472 bytes.
     - The switching in time is a floor declared as the chart's width, not the hazard ladder.
       Its segment telescope in Lean is owed (#62).
     - **Not adopted.** The choosing families decide: their charged bytes read `−3 + 12/16 + ε`
       against the egg alone and their whole stream about 7 bits above it. The gain rides on the
       floor, a switching law entered as a width (`K = 64`) and never compared with the declared
       fixed share, and it costs four times the standing for under one bit in 1,700 bytes. The egg
       alone stays F0's byte predictor. Mixing similar context models is not the lever on the rate.
  3. **Word contexts. Learned tokens as the alphabet: not adopted, September 28.** A tree over
     learned merge tokens (`hnn_tokens`: K = 256, depth 4 tokens, both chosen on choosing alone)
     codes the validation bytes `77906 + 10/16 + ε` bits above the flat byte tree (`1 + 15/16`
     against `1 + 13/16` bits a byte). Its releases hold fewer real words (836 of 1,527 against
     580 of 758), fused across merge boundaries. A token as an opaque index loses the byte tree's
     sharing: words with common spellings share no counts. Its standing is 389 bytes a cell.
     Words therefore enter as an **added** family, winning only where they are closest (candidate
     2), never as a replacement alphabet. Continuation transports stay promoted by
     `π_G P_G > π_C P_C`.
  4. **A learned lens** under source item 10.
  5. **The egg's memory, a coarser byte tree (U2's acceptance run). Adopted September 28**
     ([record](../../research/records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md)).
     The egg's byte tree is declared at 12 ticks (`f0-egg`, `F0_BYTE_DEPTH`), chosen on the choosing
     families of a fresh split over the unmerged tree and the once-reached chains released at each
     conversation's opening.
     - Validation, charged: `+224 + 12/16 + ε` against the unmerged tree (within `m = 1214`); the
       bytes `−2132 + 13/16 + ε` and the bytes with the response stops `−810 + 9/16 + ε` against the
       flat tree's bytes (the unmerged tree `−2356 + 0/16 + ε` and `−1035 + 12/16 + ε`).
     - The standing falls from 2,651 to 2,049 bytes a cell; without the readings kept beside the
       state, from 1,511 to 1,134, within the budget of 1,298. That split is now spent.
- **Standing.** Every receipt reports standing bytes a cell. A standing budget is pinned before each
  run.
- **Readings of released text, monitored and never forced** (Brandon, September 28): paired
  delimiters (quotes, brackets, backticks, bold), valid UTF-8, and the word-shape rate against the
  choosing vocabulary (`release_legibility.py`). The first releases: 24 texts and 8 typed refusals;
  580 of 758 word tokens real, against 3,139 of 3,306 in the controls; backticks even in 14 of 24,
  against 32 of 32.
- **Acceptance.** On a fresh development-family split never used for a diagnostic, the conditional
  byte-and-stop code on the validation families is strictly below the flat tree's by a margin
  pinned before the run, within the standing and passage budgets. The release readings are
  reported beside it.
- **If it fails.** The byte population stays a compression result, and F4's curated release and F5
  wait. The chase terrain (F6) carries the architecture's tests.
- **Audited September 29** (U6's restatement): the acceptance run's comparison was lopsided, its
  validation messages lay in conversations already read, and its stops were mostly record
  boundaries. The failure verdict stands, more strongly.
- **The acceptance run, September 28: the pins** (U6's first loop; committed before the split is
  generated; [record](../../research/records/2026-09-28_F0_THE_PREDICTOR_ON_UNSEEN_FAMILIES_PINNED_BEFORE_ITS_SPLIT_IS_READ.md);
  `hnn_population f0-acceptance`; Refs #73 #148 #63). A fresh split (seed
  `holonics-f0-development-families-2026-09-28-v1`; F4's, F1's, F2's two, F5's and U2's excluded);
  the egg at `F0_BYTE_DEPTH = 12`; U2's receiver; the egg's bytes and response stops, charged its
  declaration (17 + 5 bits and the learned partition's description), against the flat tree's bytes,
  charged 3, the flat tree charged no stop; the margin `m` the range of the uncharged difference over
  the spent draws read at F0's aperture before the split is generated: F1's `−279 + 10/16 + ε`, F4's
  `−726 + 9/16 + ε`, F5's `−672 + 15/16 + ε`, U2's `−812 + 9/16 + ε`, so **`m = 534` bits**; the
  standing budget 1,298 bytes a cell, whole; the passage budget ten minutes and 20 GB; 32 releases at
  hash-ordered validation responses (cap 2,048 bytes) beside the logged reply and the flat tree's
  release, read by `release_legibility.py`, the text owner-only. One amendment before the split: a
  release branches at the present incidence (`AdmittedEgg::branch_at_present`), since on F4's
  passage 8 of 32 releases were refused where the passage's declared future incidence placed a
  later letter.
- **The acceptance run, September 28: fails.** The code clause fails and the standing is past its
  budget; the byte population stays a compression result, and F4's curated release and F5 wait
  (pins `adc2cfbc`; [record](../../research/records/2026-09-28_F0_THE_PREDICTOR_ON_UNSEEN_FAMILIES_PINNED_BEFORE_ITS_SPLIT_IS_READ.md) §3;
  only counts, bits and hashes).
  - *The split.* 17,944 choosing and 4,505 validation families, none refused (membership
    `b1e322fe…`); the joined passage holds 1,047,752 cells (`d36a63ab…`, 523,747 choosing), its
    flat twin 1,046,085 bytes (`a8e4552a…`).
  - *The code* (the validation families: 20,990 human and 502,034 agent bytes, 936 response stops).
    Charged, the egg's bytes and stops lie `−290 + 0/16 + ε` bits against the flat tree's bytes,
    `[−11485719006832285584773538369701/2^95, −22971438013664571169547076739397/2^96]`, **not
    below `−534`**. The bytes alone are `−1981 + 0/16 + ε` uncharged and
    `−1931 + 9/16 + ε` charged; the 936 stops cost the egg `1640 + 7/16 + ε` bits, `1 + 12/16 + ε` a
    stop, which the flat tree does not code. Both read `1 + 12/16 + ε` bits a byte. The uncharged
    difference, `−341 + 7/16 + ε`, lies inside the spent draws' range. The whole curated stream
    lies `+2122 + 14/16 + ε` above the flat stream, charged.
  - *The standing*: 2,044 bytes a cell after the passage, **past 1,298**; the readings beside the
    state 912 a cell, and without them 1,131, within. The flat tree's is 1,296.
  - *The passage*: within: the validation reading 48,562 ms, the peak resident set 7,212,138,496
    bytes; the run 365,812 ms.
  - *The release readings* (32 releases, `release_legibility.py` against the split's 6,461-word
    choosing vocabulary). The egg: 28 texts and 4 typed refusals (3 text-codec separators, 1 at the
    cap); 1,186 of 1,513 word tokens real. The flat tree: 1,626 of 2,096 real, 24 of 32 valid
    UTF-8. The logged replies: 3,056 of 3,232. `()` balanced in 14 of 28 releases, against 11 of 32
    for the flat tree and 32 of 32 logged replies; backticks even in 13 of 28, against 15 of 32 and
    32 of 32. The longest warm release took 27,187 ms.
  - *The failure, by its measurement* (the next loop's subject): on unseen families the egg's byte
    gain over the flat tree, 1,981 bits in 523,024 bytes, is mostly spent on the stops it must
    predict, and what remains is within the draw-to-draw spread; its standing is past the flat
    tree's by the readings kept beside the state.

### F2. The field as a family (step 4; #73)

[established-bounded; source-inspected] The [F2 pin and preflight](../../research/records/2026-09-27_F2_FIELD_FAMILY_GATE.md)
found that the proposed full passage exceeds the budget and the bounded probe is below the
field's admitted `n*`. The resident exposure also lacks a per-cell rational field face for the
population's `Family` contract. A corrected `n*`-sized host field exposure read one held-out
development passage in 363,330 ms, but supplies no population field-family comparison or
adoption. The field remains dormant for text until that consumer is built. U1 built it (the
receiver's population at the HNN's port), and the adoption gate of September 28 below read it on
fresh families: the code is strictly shorter, the work fails the budgets, and the field stays
dormant for text.

- **Builds on.** `hnn::receiving`, `hnn::reference::expose`, `receiver::population` and its work
  receipts.
- **New.** A field family in `receiver::population`. Its learning covector is the declared target
  minus its own face, while `q_population = Σ_f w_f P_f` scores the passage. Its declaration is
  charged once, in the prior.
- **Acceptance.** It is adopted for text only if both hold on the pinned validation families:
  - the charged population code is strictly shorter than without the field;
  - its complete work fits the declared response and passage budgets.

  Field work, memory and code are reported separately.
- **Budget.** At the recorded costs (card about 104 ms a two-cell window), a serial field-and-
  population passage over the standing cut exceeds ten minutes. It is projected, and run as a
  bounded probe if the projection fails.
- **If it fails.** The field stays dormant for text, kept and not run, with the decision recorded.
- **The adoption gate on the receiving population, September 28: the pins** (committed before the
  split is generated and before any of its cells is read; Refs #73 #63). U1 joined the field's
  per-cell face to the population at the HNN's port, which is the consumer the preflight found
  missing: `hnn::receiving::receiving_population`, a `PortPopulation` over the tree's face `q_T` and
  the combined face `q_C`, which enters as its exact enclosure in `ℚ(θ)`, at `½/½`. No law or owner
  is added. The gate is a mode of the exposure harness (`hnn_exposure … gate f2`).
  1. *The families.* F2's split of September 27 is spent. Its validation tail was read once by the
     capacity-admissible exposure, whose model face was then the tree-and-combined mixture, with the
     tree printed beside it, so the with-and-without comparison has already been read on those
     cells. A different part of the same split, chosen after that reading, would not be fresh. The
     fresh split uses `seed = holonics-f2-development-families-2026-09-28-v2` under F4's rule
     (`development_families.py F2V2`). Each role's stream is written by
     `curated_source.py 524288 <role> F2V2`: F4's aperture, one tail of at most `2^19` cells a role,
     opening at a section letter. Its counts and hashes are recorded with the receipt.
  2. *The full gate is projected and refused.* The declared passage is the validation role at F4's
     aperture: at most `2^19` cells, so at most `2^18` two-cell windows, read after the choosing
     role's. U1's card run on the standing cut took 308,234 ms over 3,074 windows, `100 rem 834` ms
     a window. At that rate the validation role alone projects to at most `26285521 rem 2142` ms,
     43 times ten minutes and 485,521 ms more. The host is slower (359,998 ms, `117 rem 340` a
     window). Ten minutes admit 5,983 windows at the card's rate. So no full passage runs and none
     is claimed (the protocol).
  3. *The bounded probe*, at the field's admitted `n* = 6,148`, keeps F2's capacity-admissible
     shape: the last 4,096 byte cells of the choosing role's stream, then the last 2,052 of the
     validation role's, with the section letters removed (`f2_capacity_probe.py F2V2`), held out
     `[4096, 6148)`, 3,074 windows. The field is campaign one's, declared at 6,148 cells, and the
     tree is its receiver's (`D = 4`, the `½` stop prior, `L_R = 16`), as on the standing cut.
  4. *The comparison.* Both populations are declared at the passage's opening. Each scores every
     cell before that cell's own deposit.
     - **With**: the receiver's population, the tree and `q_C` at one bit each (`π = ½/½`). The
       field's declaration is charged once, in the prior, and reaches the validation cells through
       the posterior.
     - **Without**: the population over the tree alone, one family at prior one
       (`PortPopulation::new(&[0])`). Its faces are the same tree's executed faces at the same
       causal addresses (`Landmarks::receive` over the cell letters). It is read after the exposure,
       over the cells the exposure scored.
     - The charged code of the validation families is each population's per-cell codes summed over
       the held-out cells, as enclosures. *Strictly shorter* means `with.upper < without.lower`.
     - The two readings of the tree must agree: the population over it alone and the exposure's
       tree column must intersect on both parts. Otherwise the run is refused as inconsistent.
     - Beside the gate, deciding nothing: each population's whole-passage telescope (where the one
       bit is paid explicitly), the field's own face `L_C` on the validation cells, the log-odds
       `log₂(L_T/L_C)` at the join and at the end, and the field's declared description (the
       `Kt` term).
  5. *Work and memory, reported separately.*
     - With the field: the exposure's wall time by phase (the tree's read, transfers and deposit
       updates apart from the field's word and wave phases), its resident state bits, the process's
       peak resident set, and the card's memory, sampled by `nvidia-smi` during the run.
     - Without it: the population over the tree alone, its wall time and its state bits (the tree's
       and the one-family population's).
     - The field's part of the state is the resident's bits less the tree's and the population's.
  6. *The budgets.*
     - (a) The probe passage: the whole run (setup and exposure) within 600,000 ms, a resident set
       within 20,000,000,000 bytes, and at most 16 GiB on the card.
     - (b) The warm response: 60,000 ms. It is read on the declared validation passage's agent
       responses: each agent-channel part, as F0's response stops count them. The longest, `r`
       cells, occupies `⌈r/2⌉` windows at the run's mean a window. The reading excludes the
       request's own reception, so it can refuse the budget and cannot by itself admit it.
     - (c) The declared validation passage of item 2: ten minutes, at the run's mean a window.
  7. *The adoption rule.* The field is adopted for text only if the comparison of item 4 is
     strictly shorter and every budget of item 6 holds. [agent-inferred, from the protocol: a failed
     projection admits a bounded probe, never a full-passage claim; the F2 pin of September 27 said
     the same.] Budget (c) is refused by projection before the run, so **this run cannot adopt the
     field**. It reads the code and the probe's work, and names each separating term by its
     measurement. If the field fails, it stays dormant for text, kept and not run.
  8. *The run, once*, on the card: `holonics-cuda`'s `hnn_exposure … realization card gate f2`,
     alone on the idle card under the GPU lock. Its readout equals the host's line for line (U1).
     - It is projected at 308,234 to 318,378 ms for the exposure, milliseconds for the tree alone,
       under 1 GB of host memory and about 512 MiB on the card.
     - It is stopped past ten minutes (`timeout`) or past 20 GB (a memory-limited scope), and its
       partial evidence is then reported as incomplete.
     - The harness's smoke is the public development control (`held-out 6132 windows 16 gate f2`,
       32 cells, the two readings of the tree agreeing). Nothing of the fresh split is read before
       the run.
- **The adoption gate, September 28: the receipt. The field codes the validation cells strictly
  shorter, but its work fails the response and passage budgets. Not adopted; the field stays
  dormant for text, kept and not run** (the run at the pins' commit `89bc9b8b`; Refs #73 #63;
  only counts, bits and hashes are reported, and the log stays owner-only).
  - *The split* (`development_families.py F2V2`, `curated_source.py 524288 <role> F2V2`,
    `f2_capacity_probe.py F2V2`). Source SHA-256 `e1001a7e…` as F4's. Of 22,449 development
    families, 18,068 choose and 4,381 validate, none refused; the membership's SHA-256 is
    `66687b12c3c1148b50cac14106c536c7687ae65c9bcd3482c8b4844cad3b087c`. The role streams hold
    12,286,055 and 3,089,767 cells. The declared validation passage holds 523,995 cells
    (`6ca679945a7e67189ece108a81f4ce2e8fd3c6e9f54b635626f1d8c1676e8a6c`), 523,130 of them byte
    cells, with 820 agent responses. The probe's cut is
    `0a111b33e743e462dcdbcd215f2ed72fd0c0cd5bb1e9c168f79258c619fd287e` (choosing tail `743b4e52…`,
    validation tail `3b674bec…`).
  - *The run.* It ran on the card, alone on the idle RTX 4080 SUPER under the GPU lock, complete:
    3,074 windows, no budget stop, every tick balance and word balance closed. The two readings of
    the tree intersect on both parts. Bits are read at `L_R = 16` as `n + k/16 + ε`; the exact
    enclosures follow.

    | The validation cells (2,052) | With the field | Without it |
    |---|---|---|
    | Charged code | `7450 + 1/16 + ε`, `[295128431019628188705712421452793/2^95, 590256862039256553129877989108675/2^96]` | `7460 + 2/16 + ε`, `[295526465875028402633931480694427/2^95, 295526465875028402633931480695453/2^95]` |
    | Work | 328,939 ms for the run (setup and exposure), `107 rem 21` ms a window | 432 ms for the population over the tree alone |
    | Memory | resident state 6,623,232 bits (the field's part 4,982,280, the tree's 1,640,101, the population's 851); peak resident set 502,538,240 bytes; at most 739 MiB on the card | 1,640,532 bits (the tree's 1,640,101 over 42,940 nodes, the population's 431) |

  - *The code: strictly shorter.* With − without is `−11 + 15/16 + ε`,
    `[−99508713850053482054764810665/2^93, −796069710800252137984972280179/2^96]`: the field's family
    codes the validation cells between 10 and `10 + 1/16` bits shorter. Both read `3 + 10/16 + ε` a
    cell. Beside it, deciding nothing:
    - the field's own face `q_C` codes the validation cells at `7450 + 1/16 + ε`, with
      `L_C − L_T = −11 + 15/16 + ε`;
    - on the 4,096 choosing cells, with − without is `−15 + 3/16 + ε`, and `L_C − L_T` at the
      join is `−16 + 3/16 + ε`, so the population enters the validation cells almost wholly on
      `q_C`;
    - over the whole passage, where the prior's one bit is paid explicitly, the telescopes read
      `22988 + 11/16 + ε` with the field and `23013 + 8/16 + ε` without, a difference of
      `−25 + 2/16 + ε`; the log-odds at the end are `−26 + 2/16 + ε`;
    - PPM-2 codes the validation cells at `7858 + 0/16 + ε`; the population with the field less
      PPM-2 reads `−408 + 0/16 + ε`;
    - the field's declared description, the `Kt` term that the gate's prior does not charge, is
      1,439 bits.
  - *The work, by phase* (milliseconds over the run, per window as quotient and remainder over
    3,074).
    - The tree's own phases (its read, transfers and deposit updates) take 7,520 ms. The rest of
      the phases' 286,948 ms is the field's, with both populations' scoring inside the compare.
    - The card's word (the refine read) takes 6,858 ms, `2 rem 710` a window.
    - The host's deposit of the successor constitution takes 166,708 ms, `54 rem 712` a window:
      more than half of the run. The re-read takes 41,667 ms, the compare phase 33,896 ms and the
      composition 15,851 ms.
    - With the field, the run takes 328,939 ms against the tree alone's 432 ms: a ratio of 761,
      remainder 187.
  - *The budgets.*
    - (a) The probe passage: within its budget. It took 328,939 ms, against 600,000 (margin
      271,061). Its peak resident set was 502,538,240 bytes, against 20,000,000,000. The card's
      total use, sampled every 250 ms, peaked at 2,060 MiB against 1,321 MiB before the run, so
      the run held at most 739 MiB there.
    - (b) The warm response: **past its budget.** The longest agent response has 18,873 cells:
      9,437 windows, 1,009,824 ms at the run's mean, 949,824 ms past the minute. The minute admits
      560 windows at that mean. 39 of the 820 responses are past it; the longest that fits has
      1,113 cells.
    - (c) The declared validation passage: **past its budget.** It has 523,130 byte cells: 261,565
      windows, 27,989,242 ms at the run's mean. That is 46 times ten minutes and 389,242 ms more.
      Ten minutes admit 5,607 windows at that mean.
  - *Verdict.* **Not adopted.** The code is not the separating term: the field's family codes the
    unseen validation families strictly shorter than the tree alone. The separating term is its
    work: `107 rem 21` ms a window, against 432 ms for the tree's whole passage. More than half of
    each window is the host's deposit of the successor constitution (`54 rem 712` ms), not the
    card's word (`2 rem 710` ms). The declared validation passage needs 261,565 windows where ten
    minutes admit 5,607 at this rate. The field stays dormant for text, kept and not run. The
    receiver's population still weighs it at the HNN's own port.


### F3. The resident population (step 5; #76)

- **Scope.** The curated population's selected family, its mixture and its receipts, ported as a
  bounded resident path. Each family that stays on the host is named, with its reason in #76.
- **Acceptance.**
  - Faces, code enclosures, deaths and receipts equal the host's on pinned fixtures and on one
    curated passage.
  - The report gives population-only card time against population-only host time, the transfer,
    the peak card memory and the capacity census.
  - Acceleration is claimed only if the resident path is faster within capacity.
- **If no family completes resident.** F3 fails, and a host Athena may still proceed.


### F4. Release (campaign 5 into step 8)

[established-bounded; measured] The [pinned split and receipt](../../research/records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md)
record one held-out development-family passage. The F4 failure branch applies: the score-identical
next-face view is built, but the text-release carrier is incomplete, and the charged validation
stream is above the flat control. The evaluation partition remains closed.

[established-bounded; F5 development continuation] A [private diagnostic](../../research/records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md)
now branches contemporary choosing standing, plans request incidence, samples a family once from
the posterior enclosure and follows its exact face to a section stop. On one response a fresh
branch verified the population's scored face before all 179 bytes and the stop and checked UTF-8
and the append-scalar square in 15,826 ms warm. The posterior's unresolved draw region,
producing-key/causal relation, compatible-source fibre and product health are retained as missing
terms; this is not F4 acceptance.

- **Builds on.** `receiver::release`, the generic release law.
- **New.** The population's text-release consumer.
- **Law.** A request conditions the same face that scores a complete response, its stopping section
  included: `P_release(y | request, Θ) = P_scored(y | request, Θ)`. Each release carries:
  - its decoder;
  - the keys;
  - its causal provenance (the egg and keys that produced each face);
  - the grain and fibre;
  - a typed refusal where it declines.

  `D E = ρ` and `E_next T = U E` are checked, or a separator is returned.
- **Terrain acceptance.**
  - Exact continuation is required only on deterministic terrain (the moiré, the arithmetic),
    after a future-equivalent key is located.
  - On stochastic terrain the conditional faces are compared with the known source, never one
    drawn stream against its entropy.
- **Curated.** Development responses are inspected against a request-aware retrieval control:
  answering with the most similar earlier request's recorded response.
- **Deadline.** A warm-response deadline is pinned.
- **If it fails.** The machine is a predictor, not yet a releasing product.

- **Second stage, after the first receipt** ([review](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#143-release)). The release becomes
  receiver-conditioned: `Q_R(e | s) ∝ 1_(A_K(s))(e) P₀(e | s) L_R(z | e, s) 2^(−c_R(e))`, the unique
  minimizer of `D(Q ‖ P₀) + E_Q[c_R − log₂ L_R]` on the viable emissions. Then
  `P_release = P_scored^release = Q_R`, timing and stopping included, and `P₀` is the reported
  control. Each section compares release, waiting, a viable probe and a typed refusal, each with a
  declared cost. The receipt carries `P₀`, `Q_R`, `Z_R`, the comparison and the delay price. A
  cheaper later turn is not by itself value.


### F5. Athena-0: the first product outcome (step 8; #148)

[established-bounded; development only] The [F5 pinned diagnostic and gate](../../research/records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md)
have a one-protocol atomic exterior checkpoint/replay fixture, a certified private native
request path and a 32-request diagnostic pass: 24 provisional UTF-8 candidates, eight typed
failures, 314,527 ms of choosing preparation plus warm work, and no evaluation read. Eleven of
those requests have unresolved declared parents; the other 21 have one-occurrence context.
The split was used to refine the release route, so it is spent for diagnostics and cannot serve
as F5 acceptance. The product protocol refuses the provisional text for missing native health,
key/causal provenance and compatible-source fibre. Versioned exact codecs now cover the tree,
boundary/admitted eggs and a tagged population in small continuation fixtures. On the actual
choosing standing, the full tagged stream occupies 6,256,005,986 bytes; its development restore
passed the next-face/receive square at 16,287,236,096 bytes sampled peak RSS. An independent cold
restore, a memory-bounded single-file atomic native protocol join and truthful product receipts
remain open; the JSON/base64 fixture is not the large-state path. Freeze the law
and pin a fresh untouched development split before F5's acceptance pass or evaluation.

- **Definition.** A local interaction on this machine (one RTX 4080 SUPER of 16 GiB, 20 GB of RAM
  admitted). It accepts a visible human request and its declared conversation context, and returns
  a relevant, grounded text response or a justified refusal, with a receipt.
- **Built for it** (the lessons record's requirements):
  - one command vocabulary with human, JSON and JSONL views;
  - one atomic checkpoint of standing, cursor and pending comparisons;
  - exactly-once output and byte-identical resume;
  - each response's numerical health (radius, robust count, operator bound, contraction),
    provenance and costs by kind, refusing any face that covers the simplex;
  - private sources and diagnostics kept owner-only.
- **Gates before the evaluation partition opens.** The pinned retrospective requests and the
  restart check pass on development.
- **Evaluation, once.** On every eligible evaluation request, Athena releases before its recorded
  reply is read. **Brandon judges** (September 27: "I'd want to do it"), blind, under a rubric
  frozen before the split is read.
  - For each request he sees two responses side by side in a hash-seeded random order, Athena's
    and the retrieval control's, with nothing that names their source.
  - He marks each response as answers, justified refusal, or fails, and marks which of the two is
    better or that they tie.
  - The judging surface shows him the request, its declared context and the two responses, and
    nothing private beyond what he already owns.
  - The unblinding key is written after his marks are committed.
- **Acceptance.**
  - More than half of the outputs answer, or justifiably refuse; an answerable refusal counts as a
    failure.
  - The releases win more than they lose against the request-aware retrieval control built from
    development only.
  - Nothing private is disclosed.
  - A warm response returns within one minute, within the declared memory limits.
- **Reported beside it, not as acceptance.** The conditional code of the recorded replies, against
  the request-blind population, PPM-2 and the flat tree.
- **If any gate fails.** Athena-0 has not been reached.


### F6. Motion: the chase terrain, then the motor chart (campaign 4; #27, #148)

[definition; agent-inferred; Brandon's derivation, September 27, [record](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#13-the-chase-terrain)]
The machine has only read recordings; here it first moves, against another's constitution.

- **Builds on.** `holarchy::terrain` (terrain with known truth, the `Switching` pattern of declared
  families), `receiver::population` (families, mixture, dormancy's fixed share, composition),
  `receiver::release` (`DecisionRule`), `holarchy::gluing`, `geometry::screw` and Lean
  `Transport/SerialScrewChain`.
- **New.** A chase terrain, `holarchy::terrain::chase`:
  - an exact, bounded 2D arena over a rational lattice with a declared tick, each cell with a
    friction class `μ` from a declared finite set of rationals. The walls make forced turning
    possible: in an open arena a faster runner moving straight away is never caught;
  - a fast runner (speed bound `v_R`) whose velocity change per tick is admitted only if
    `|Δv|² ≤ (μ g h)²` on its cell, which bounds a pure turn's radius below by `v_R²/(μg)`. A demand
    beyond traction slips (a declared hybrid law): the runner keeps its tangent velocity for a declared number of ticks. Its
    evasion navigator and key are drawn from a declared family, which is the terrain's truth;
  - the chaser, the machine: slower (`v_C < v_R`), of a larger traction class, every emitted motion
    satisfying its own bound exactly;
  - two switches: a lag channel (observation `d` ticks late) and a faulty sensor (one of three
    independent, time-aligned channels reports a rotated heading on declared aeons; two channels
    detect a fault but cannot locate it).
- **Law.**
  - Reception: the population reads the runner's passage and selects its constitution (speed bound,
    traction per friction class, slip law, policy family).
  - Action (amended by U3's second loop, September 28): each chaser motion is released through the
    one release law (`receiver::release`) on the capture-within-`m` reading over the selected fibre.
    A capture the basin certifies over every member is `Released` at tolerance zero. Beyond it the
    law asks the offered probe (`Ask`): the motion of greatest `I(Θ; Y | h, do(a))`, offered where it
    separates the fibre strictly more than the commit, compared exactly as `∏|c|^|c|`. Where no
    probe is offered the law holds. The probe is emitted only within the declared price of a tick,
    `K(u_p) − K(u*) ≤ d·|Θ|` (the Bellman stop law of §14.3, read one step deep). Otherwise the
    machine commits to the cornering move, the declared separate arm whose separating term is the
    price. Each emission carries its predicted consequence, and the directed covector (predicted
    against unfolding) is read at the action.
  - [historical] Superseded September 28 by U3's second loop: "Action: each chaser motion is released
    as a threshold commit, a sequential test on accumulated log-odds whose threshold is priced by the
    declared cost of a tick." Why, from the mathematics:
    - Under the declared deterministic candidate laws with their escape, every member of the
      selected fibre has the likelihood `(1 − η)^n` (Lean `Population.survivors_share_one_likelihood`).
      So the log-odds between members are identically zero, and a threshold of at most one
      contradiction's `log₂((1 − η)(A − 1)/η)` bits is crossed exactly when the fibre is one member.
    - The test reads the family's identity, which is finer than the action's consequence. The capture
      reading certifies the consequence over a plural fibre (143 of the 152 certified releases on the
      acceptance seeds, 138 of 144 on the choosing seeds), where the test would still be sampling.
      Every single-member tick was already certified.
    - Wald and Wolfowitz's optimality holds only for two hypotheses under stationary, independent,
      passively sampled observations (§14.3). Here the chaser's move selects the observation. The
      general law is the Bellman comparison, which the built rule reads one step deep.
  - Deposition only at the locus a covector reached: a loop-closure reading across the three
    observation channels attributes each error to the mover or to a channel. The channel menu meets
    the separation condition: a defect on at most `k` edges is located uniquely only when the
    circuit matrix's kernel holds no nonzero vector of support at most `2k`.
  - Retention is action-sufficient: no merge of runner constitutions that an admitted probe would
    separate. Where the fibre is wide, the chaser may emit the probe with the greatest
    `I(Θ; Y | h, do(a))`.
  - Capture: the agents' quadrance is at most a declared capture radius squared.
- **Reception acceptance.** On hash-seeded arenas the selected fibre is future-equivalent to the
  truth under the admitted actions; the exact family is required only where a probe separates it.
  Its code is within a declared margin of the truth code, and strictly below the landmark tree
  reading the same passage.
- **Action acceptance.**
  - Over pinned seeds, capture takes strictly fewer ticks in sum, and in more than half of the seeds,
    than both controls under the same traction bound: pure pursuit and constant bearing.
  - The traces show turns forced across low-friction cells, with the runner's slips counted.
  - With the switches on, capture still beats both controls, the fault is located on exactly the
    aeons it is active, and lag-caused errors deposit nothing in the chaser's constitution.
- **The switches and their attribution, built and read once** (September 28; #27; receipts in the
  notebook README, `hnn_chase switches`; the owners `holarchy::terrain::sensing`,
  `pursuit::Pending` and `receiver::population::chaser`, "The lag" and "The attribution").
  - *The switches* ([definition; agent-inferred]): three time-aligned channels read the runner's cell
    as its kind, the line of sight and the heading in their own frames. The lag `d` delivers tick
    `τ`'s readings once `τ + d` has moved (the controls read the runner at `t − d`). The faulty sensor
    turns one channel's frame by `i^a` on the odd aeons of a drawn switch clock (`SwitchTruth`); the
    frame, not the velocity alone, since a turned zero velocity makes no error to locate.
  - *The separation check* ([proved-derived]): the three-channel menu's circuit matrix
    `C = [[1, −1, 0], [1, 0, −1], [0, 1, −1]]` over `ℤ/4` has `ker C = {(c, c, c)}`, so no nonzero
    kernel vector has support at most `2 = 2k` and one turned frame is located with its turn; `(1, 1, 1)`
    breaks `k = 2`, `(1, 1)` breaks two channels. The lag `(d, d, d)` lies in `ker C`: no channel
    circuit sees it, and the motor record closes it.
  - *The attribution* ([definition; proved-derived]): the channel loop's locus is the channel; the
    mover's loop (the contemporary fibre against the port at the reading's tick) is the runner's
    constitution, the only deposit; the lag's loop deposits nothing,
    `q − p_act = (q − p_con) + (p_con − p_act)` with `q − p_con` alone consumed. Under the lag the
    capture basin reads the lagged information structure (withheld cells, classes by the cell the next
    reading reveals, capture member by member); at `d = 0` it is the unlagged recursion, and `action
    trace` is unchanged line for line.
  - *Pinned before the run* (commit `95a8864a`): seeds `20261301 + s`, `s < 64`; `d = 1`; the fault's
    aeons uniform on `1..=4`; the switch bullet as written.
  - *The run* (once; 162,402 ms at a 269,180 kB peak; 63 chased seeds, 20261325 refused): with the
    switches on the machine takes 646 capture ticks against pure pursuit's 19,255 and constant
    bearing's 4,713, fewer than both at once on 38 of 63 (off: 611, 17,034, 1,949; 36 of 63). The fault
    is located on 111 of the 111 active aeons read and on no inactive one (264 of 264 active ticks,
    none wrong, no false alarm). The constitution equals the prompt one on the true cells on 63 of 63
    seeds; 48 of the 126 action-time misses are the lag's and deposit nothing. 589 of 589 released
    bounds are kept. **The switch bullet passes as written.** The action acceptance as a whole still
    fails on its first bullet at the pinned acceptance seeds (7 of 16), unchanged.
  - Owed in Lean (#62): the localization condition and its three-channel instance, the lagged basin's
    exactness, and the attribution's covector split.
- **Reported beside it, not as acceptance.**
  - The cornering receipt: the runner's robust viability kernel in the arena, tick by tick, under
    the machine's play and under each control. Capture should come from shrinking it.
  - Brandon's own play through a small exact interface, with real intervals: the human baseline,
    and data with real flux.
- **Budget.** A few thousand ticks per seed in exact arithmetic on the host, projected against ten
  minutes and the host memory before it runs. No card is needed.
- **If it fails.** A reception failure locates the birth problem on terrain whose truth is known. An
  action failure leaves a receiver without a controller, reported as a terrain result.
- **Then the motor chart.** Pinned before fitting: a public recording, its skeleton, its units, the
  horizon, the split and a constant-velocity control. The HNN's motor consumer preserves the ordered
  screw transport and `⟨w, Jθ̇⟩ = ⟨Jᵀw, θ̇⟩`, and releases a reachable endpoint at its declared grain
  or returns the complete joint fibre and residual. Acceptance: a held-out endpoint residual strictly
  smaller than the control's, within budget; otherwise the exact geometry is reported with no claim
  of motor usefulness.

## Protocol

- **Pinned families.** Before each new validation the item pins disjoint development families for
  choosing and for validation, drawn from the dataset's development partition by a declared
  hash-seeded split. It also pins the consumer, the charges, the baselines, the acceptance and a
  deadline.
- **The evaluation partition.** F5 alone opens it, once, after every product gate has passed on
  development.
- **Budgets.** Each full passage is projected before it runs, against ten minutes, 20 GB of host
  memory and the card's 16 GiB. A failed projection admits a bounded probe, never a full-passage
  claim.


## Rules of the rebuild

- **Build forward from the elementary objects.** Each new owner states which object and law it
  implements ([operator contract](../ELEMENTARY_OBJECTS.md#operator-contract)), and which part of
  the line it serves: the navigators, terrain, kernel, cokernel and landmarks it touches.
- **Port deliberately.** A law or kernel is ported from history (`13f8c734`) when a step needs it.
  It is read, rewritten against the current objects, and tested by the law it implements. Nothing
  is restored wholesale, and nothing is kept for compatibility.
  - Where to look: the census at `13f8c734` locates history's owners
    ([`RUST_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/RUST_R0.tsv), [`LEAN_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/LEAN_R0.tsv)),
    and so does the manifest on `archive/leftovers-2026-09-24`.
  - Each port is recorded in its step's issue as history path → new owner → law → test.
- **Do not port** what the retention audit and the lessons record retired:
  - the per-occurrence tape and frozen-cut replay;
  - `returns` journals and completed-update archives;
  - slot, session and episode wires;
  - byte and nibble codecs;
  - Q/K/V caches and foreign forward graphs taken whole;
  - any Lean in the HNN pipeline;
  - floats inside a law.
- **One library for the laws, one backend for the card.** `holonics` builds without CUDA.
  `holonics-cuda` depends on it and realizes its operations. Brandon's `codex/apple-silicon`
  (September 7, built on the retired engine) becomes `holonics-apple`. It implements the HNN
  execution port only after the host reference exists, with parity per law.
- **The hardware surfaces advance with the laws** (Brandon, September 25: "you should not have
  been neglecting the hardware surfaces"). The resident realization (step 5, `holonics-cuda`, and
  later `holonics-apple`) is not scheduled after step 4: each campaign's laws land with their
  device kernels and host parity checks, and an exposure runs resident. The host reference stays
  the parity target; the measurement that took one core for hours (the lattice word's
  [record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md), addendum) is the lesson.
- **Lean first for new mathematics.** A new law lands with its Lean statement, or names its
  obligation in #62.
- **Tests are written per law** as each owner is built: one fast test per stated law, plus one
  host/device parity check per kernel family. An inherited test stays only if it checks a stated
  law of its owner. The testing protocol (Brandon, September 25: "I wouldn't tolerate this"):
  - a test proves its law on the smallest fixture that exhibits it; no test builds a campaign's
    declared field;
  - a test runs in well under a second in a debug build, and the whole `cargo test -p holonics`
    stays within seconds; a test that needs longer is a measurement;
  - measurements (bit curves, timings, real cuts) are notebook examples run once in release,
    reported with their command and result as receipts, never gates;
  - a check that an optimization changes no value runs once on the real case as a receipt, and the
    suite keeps only its small-fixture law;
  - cost is a property of the representation: a law that is local and block-sparse is implemented
    and certified block by block, never by assembling a dense global object (guard 14).
- **A development harness decides; the held-out pass confirms once** (Brandon, September 26: "the
  lean needs to consolidate, issue hygiene is also bad, handle the step 4 'behind its own pace'
  thing properly as well"; the rules are agent-inferred, [record](../../research/records/2026-09-26_STEP_FOURS_PACE_AND_THE_LIBRARY_CONSOLIDATING_WHILE_IT_GROWS.md)).
  - Every predictive hypothesis (a letter family, a depth, a grain, a mixture component) is first
    measured prequentially on the development cells with `hnn_landmark`. The full exposure, host
    and card with its held-out pass, runs once per campaign at its end, and otherwise only when a
    law changes the word itself.
  - Law gates are the laws' own tests: a worker runs the gates of CLAUDE.md for what it changed,
    lowest first; the primary integrates on those receipts and re-runs only the gates the
    integration itself changes.
  - Campaigns on disjoint owners run together, each with its own success receipt. Each campaign's
    new law lands at its consuming owner and retires any duplicate in the same change.
- **Exact arithmetic.** No floats inside a law or the machine (CLAUDE/AGENTS, governing laws).


## History

[historical] The [construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
keeps, word for word, what this plan replaced on September 28: the status of September 27, the forward
plan F0–F6 with its receipts, why the repository was reset, the order of steps 0–8, the laws found
alongside them, and the step-4 design with its five campaigns, its port map and its retired choices.
The measurement protocol and the guards moved to [THE_MACHINE](../THE_MACHINE.md#measurement).

### The Decisions index

In this table, (a) to (e) and (h) name sections of the construction record's step-4 design; (f) is
[THE_MACHINE's measurement](../THE_MACHINE.md#measurement) and (g) its
[guards](../THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible); "Rules of the rebuild" is
above.

[historical] Until September 27 this plan kept a numbered log, Decisions 1 to 39. Brandon,
September 27: the numbered Decisions were a habit of the agents, not his instruction. The
[unity audit](../../research/records/2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md) dissolved the log: each law now lives in its guide or owner with its source,
each measurement in its dated record, and each retired choice in (h). Dated records, the notebook
and some Lean module docs keep the numbers, and this table resolves them; the Lean names that cited
them now state their law (`depth_one_is_the_whole_cell_table`, `first_arrival_is_the_full_tree`,
`compacted_is_the_full_tree`, September 27). A Rust owner's module doc is
`crates/holonics/src/hnn/<name>.rs`, except the receiving tree's, which is
`crates/holonics/src/compression/landmark/context.rs`.

| # | Subject | Where it lives now |
|---|---|---|
| 1 | The medium changes only by deposition and, at an aeon boundary, by the collapse | (a), "The light is the change" (law and source); guard 11 |
| 2 | Selective stepping; participation fixed by keys | (a), "Stepping is selective" and "The nonlinearity lives in finitely many key and lock classes" |
| 3 | Local propagation | [THE_MACHINE](../THE_MACHINE.md), "No global solve" (Brandon's rulings); (a), "The causal cone" |
| 4 | Changes, not states | (a), "The light is the change" |
| 5 | Participation is the junction Swing's anchor, one exponent per contact | (a), "Participation is the Swing's anchor" |
| 6 | Retention is the collapse onto what the admitted future distinguishes | (a), "Retention" (law and source) |
| 7 | Exact inside, grain only at the face | (a), "Exact charts" (law and Brandon's rulings) |
| 8 | Rings close by default | (a), "A ring is a closing rotor by default" (law and Brandon's ruling) |
| 9 | The contact carries its own constitution | (a), "The contact carries its own constitution" |
| 10 | Keys lead; key location | `hnn::keys` module doc; (d), campaign 1, "Data → menu" |
| 11 | Far fields carry moments | (a), "Far fields carry moments" |
| 12 | Release goes through modes | (a), "Release through modes" |
| 13 | The pending read | (a), "The pending read" |
| 14 | The port | (c) |
| 15 | The return keeps the word's own waves or checkpoints | (a), "The return holds no tape" |
| 16 | Every campaign on the standing real cut (Brandon, August 26) | (f), "The cuts and their protocol" |
| 17 | Owners, not new nouns | (a), "The types `holonics::hnn` adds" |
| 18 | `GeneratorSourceEpisode`'s directed-contrast law moves before the file retires | (b), "Retired with campaign 1" (done; the file is retired) |
| 19 | Guards are types and lints, not source scans | (g), introduction |
| 20 | Campaign order | (d) |
| 21 | Campaign 1's declarations | (d), campaign 1 |
| 22 | Deposition on a declared carrier lattice | Lean `HNN/LatticeDeposit`; (a), "The deposited constitution, on its declared carrier lattices"; [record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md) §5 |
| 23 | The standing real cut | (f), "The cuts and their protocol"; `research/notebook/hnn_design/standing_cut.py` |
| 24 | Every transient and inverse on a declared lattice with a certified residual | `hnn::chart` module doc, Lean `HNN/LatticeWord`; [record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md), addendum |
| 25 | The hardware surfaces advance with the laws (Brandon, September 25) | Rules of the rebuild |
| 26 | Campaign 1's first repair | (h); its open stands in `hnn::moment`; [record](../../research/records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md), addendum |
| 27 | The region table | (h); Lean `HNN/RegionCounts`; [record](../../research/records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md), addendum |
| 28 | The landmark tree (Brandon, September 25) | `compression::landmark::context` module doc; merges in (d), campaign 5; [derivation](../../research/records/2026-09-25_THE_COMPRESSION_IS_OF_LANDMARKS_A_TREE_COCYCLE_AND_MERGES_PRICED_BY_THEIR_CODE_LENGTH_PAIR.md), [measurement](../../research/records/2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md) |
| 29 | Prequential scoring | (f), "The cuts and their protocol"; `compression::landmark::context`, "The measurement is prequential" |
| 30 | The likelihood mixture; the source's normalized open | `hnn::receiving::receiving_population` (U1; the carried-ratio `Mixture` at `19f1eb61`), `hnn::moment::PopulationChart`; [record](../../research/records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md) |
| 31 | Step 4's pace (Brandon, September 26) | Rules of the rebuild, "A development harness decides"; Order, step 7; [record](../../research/records/2026-09-26_STEP_FOURS_PACE_AND_THE_LIBRARY_CONSOLIDATING_WHILE_IT_GROWS.md) |
| 32 | The declared stop prior | `compression::landmark::context`, "The declared stop prior"; [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §1 |
| 33 | The Born face | (h); [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §2 |
| 34 | Weighing is local | `compression::landmark::context`, "Weighing is local"; (h); [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §3 |
| 35 | The wide cut | (f), "The cuts and their protocol"; [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §4 |
| 36 | Second-arrival founding | (h); [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §5 |
| 37 | Stored at the faces where paths part | `compression::landmark::context`, "Stored at the faces where paths part"; [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §6 |
| 38 | The loaded resonator | `hnn::ring` module doc; [THE_MACHINE](../THE_MACHINE.md), the egg paragraph; [record](../../research/records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md) |
| 39 | A landmark's storage has a capacity | `compression::landmark::context`, "A landmark's storage has a capacity"; [record](../../research/records/2026-09-27_A_LANDMARKS_STORAGE_HAS_A_CAPACITY_AT_ITS_CEILING_IT_CARRIES.md) |
