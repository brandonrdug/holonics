# The field's entries take only the encoded source, and the folded fixtures are re-derived

**Date.** October 5. **Issues.** #73, #148, #76, #63, #62. **Lane.** E of U6, phases 2 and 3 (the boundary's
join, after the type of the [located transport record](2026-10-05_THE_LOCATED_TRANSPORT_EACH_OCCURRENCE_STEPS_THE_RINGS_BY_ITS_LOCATED_ADVANCE.md)
§10 and Codex's source entrance, #377). **Grade.** [definition; agent-inferred] for the entries and
the fixtures' choices; [measured] for the counts, quadrances and receipts below.

## 0. What was built

[definition; agent-inferred] THE_MACHINE guard 9's entries take `hnn::encoding::Encoded` only:
`Field::selective_step`, `Current::step`, `SourceMoment::ingest`, `ExecutionPort::{ingest,
locate_keys, compare}` on the host reference and the card, `hnn::keys::{locate_keys,
station_pairs, damaged_station_pairs}` and the crib helpers, `hnn::ratio::target_phases`,
`hnn::receiving::clock_letters`, the exposure's `Cut` and `Word::compare_contact_storage`. Outside
the crate a `DamagedPassage` is built only from an `Encoded` and its erasures. `Field::admit` refuses
a passage encoded against another field's source rings, with more classes than the field's `|A|`,
or with a located helix that is not the field's rings (`HnnError::Unadmitted`). `PortChart` with its
residue constructor, `one_hot`, both copies of `codes` and `HnnError::CellNotOneHot` are deleted.

**The located step.** An occurrence of the located route steps ring `g` by its class's digit plus
the carry, `a_g(c) + carry_g ≤ d_g`; `SelectiveStep.ticks` is `Vec<u64>`, so each digit, section
flux and winding is exact. The squares `D E = ρ` and `E T_a = U_a E` are checked on the lift the
step reads and the lift it reaches (`Encoded::check_step`, the encoding carried with its chart's
receiving forms and transport index per class). An identity steps by the lock's fit, as before.

**Where the fold is refused.** At the entry, not at the declaration: `Encoded::{identity, through}`
refuse classes past a source ring's period (`EncodingError::Fold`) and `Field::admit` reads the
source rings. `Field::declare` keeps declaring a field whose `|A|` exceeds a source period, since it
reads nothing then; Codex's source-entrance fixtures declare one and must stay unchanged. On a
non-source ring a class at or past `d_g` reads the port `d_g`, which no lock admits, and it is no edge
of that ring's key menu (`hnn::keys::crib_menu`).

**Campaign 1.** Its byte alphabet existed only through the fold (256 codes on a source ring of
period 5). `FieldDeclaration::campaign_one` reads five classes: `|A| 256 → 5`, `n* 6,148 → 190 =
2·5·19` (`hnn::tests::moment::campaign_one_capacity_is_certified_at_its_crossover`, which keeps the
formula's `6,148` at `|A| = 256`), its tree's widths `B = 3`, `M_p = 49`, `W = 35`. A text exposure is
refused until its encoding is founded: `hnn_exposure` tries the one route (a located chart over the
bytes on the helix of its rings, `5·7·11·13 = 5,005` past the location's ceiling) and reports the
refusal as its result, and `executed text` and `executed text-repair` report guard 9's refusal. The
card's standing-cut lockstep (bytes) is retired; its source is at `f91666c0`.

**The card.** Its port passes the admitted `Encoded` to the card's ingest, which steps by
`digits(A) + carry` on the located route (Codex's `hnn_moment_ingest` and `ResidentMoment::ingest`,
adopted in phase 3, §4). The located refusal is gone.

## 1. The reproduction acceptance

[measured] #375's validation reads on the keys states written again (seeds `2_026_093_032`, `035`,
`038`, 64 requests, both keys states), each under its committed pin
(`research/runs/states-written-again/evaluate-validation-<terrain>.pin`, guard 22), at this build:

| Terrain | Sections against #375's receipt | Wall (ms) | Pin deadline (ms) | Threads |
|---|---|---|---|---|
| order-2 | byte-identical | 80,680 | 108,000 | 12 |
| alternation | byte-identical | 87,762 | 120,000 | 12 |
| line | byte-identical | 83,010 | 123,000 | 12 |

Receipts: `…_receipts/reproduction/` (the script, the logs, the comparison and the listings' SHA-256).
The terrains enter through their declared identity (`KnownTruth::cyclic`, `Encoded::identity`), whose
stepping is the lock's fit on classes below the period-60 rings: the fold never acted there.

## 2. The folded fixtures, re-derived

[measured; agent-inferred] The in-crate chain (rings of periods 2, 3, 2; `|A| = 4`; source ring 0)
read its four classes on a period-2 source ring through `c mod 2`. Two fold-free fixtures replace it:
- **the chain** (`hnn::tests::learning::chain`): the source ring of period 4 with lock `{0, 2}`, so
  every ℤ/4 test word keeps its classes and each class fits the source ring as it did under the fold
  (`n* 134 = 2·67`, against `71`);
- **the two-class chain** (`chain_two`, `chain_two_of`): the old geometry, rings of periods 2, 3, 2
  with the same channels and receiver, reading the two classes its period-2 source ring holds
  (`n* 70`, `31` without the pair offset).

The CUDA port tests' chain is the chain on the quarter turns (source period 4, lock `{0, 2}`); the
card's moment-parity chain reads two classes.

**Why the period-4 chain moves the regime** [measured]. The test support places a ring's nodes on
the 65-circle (`x² + y² = 65`). With a source ring of period 4, contact 0's pair quadrance reaches
`Q = 98` (at lift `[3, 0, 0]` and at `[3, 3, 1]`); on the two-class chain it is at most `52`. A
contact's conductance is `κ_a = 2^(−β_a Q_a/2)` (`hnn::propagation::contact_exponent`, `β_a = 2`), so
the word meets `κ = 2^(−98)`: a 4×4 operator of the word carries the dyadic denominator `D = 2^101`
(after deposits `2^112`), and with the chart exponent `L_c = 28` its integer scale `D·2^(L_c) = 2^129`
passes the 128-bit word (`hnn::chart::Operator::scale`, `chart.rs:422`), at the declared opening on
the word `[1, 0, 3, 0, 0]`. Below the lattice grain the same conductance shuts the path: on
`[1, 2, 3, 0, 2]` the period-4 chain reaches `[3, 1, 0]` and the word's change stays on ring 0 over
four ticks, where the folded chain reached `[3, 3, 1]` (class 3 fitting ring 1 as `3 mod 3 = 0`).

**The nine tests** (each claim re-derived on the unfolded fixture):

| Test | Class | What holds, and why the old number or fixture was the fold's |
|---|---|---|
| `constitution::every_family_steps_by_its_certificate` | (a) | Its precondition, the covectors reach every family, holds on the two-class chain, where every certificate holds. On the period-4 chain `[1, 2, 3, 0, 2]` shuts the path (receiving gradient zero, no family steps), and the word reaching the folded lift overflows the carrier. The word is read on the two-class source ring (`[1, 0, 1, 0, 0]`). |
| `constitution::the_budgeted_carry_accounts_for_every_update` | (a) | The ledger identity held on every fixture; the clause that the run moves the receiving prior needs the path open. `chain_run` runs on the two-class chain; its five other consumers pass there. |
| `receiving::r_opens_at_zero_and_learns_from_the_first_deposit` | (a) | On the two-class chain the second compare's covector reaches `E`; on the period-4 chain the drawn cells leave the path shut. |
| `receiving::the_receiving_face_codes_within_one_bit_of_the_better_face` | (a), carrier | The exposure reaches the `2^129` scale on the period-4 chain; the claim holds on the two-class chain's exposure cut. |
| `reference::a_reached_contact_family_moves_or_is_named_a_rounding_refusal` | (a) | The return reaches contact 0 on the two-class chain (its words read on two classes); on the period-4 chain the word's change never crosses contact 0. |
| `prior_carry::an_exposed_located_chain_reads_its_pair…` | (a), carrier | The exposure reaches the carrier's edge on the period-4 chain; the located prior moves on the two-class chain. |
| `chart::a_deposit_moves_the_charts_by_warm_refinement` | (a), carrier | Its draws (material 26, cut 27) reach `2^129` on the period-4 chain; on the two-class chain they refine warm, every certificate at the target. |
| `reference::the_chained_balance_closes_and_the_chain_is_dissipative` | (b) | Restated on the period-4 chain, which exercises the carry (reflected power positive): it closes, is dissipative and the lift only emits at all thirteen receptions. Retired: `work = −reflected` and the stronger reading at every reception, which held because no deposit moved a contact's storage on the folded chain (`work = deposition + ingest`); the honest chain's deposits move it. |
| `prior_carry::at_rest_the_cards_chain_holds_its_prior_and_under_the_carry_it_moves` | (b) | Restated as `at_rest_a_map_that_never_leaves_zero_holds_its_prior` on the two-class chain: every read holds `k = 6` for want of curvature. Retired: "under the carry the same cut moves the prior", a fact of the folded fixture's magnitudes (two-class chain: 19 reads under the carry, none moved; period-4 chain: the map leaves zero at rest). |
| `reference::the_carry_passes_each_receptions_end_to_the_next` | (c) | Defect, below; its cause located and the claim restated (§2a). |

Carrier verdict: the three overflows are fixtures larger than their claims need. None of these claims
is about the carrier, and each holds on the two-class chain, whose quadrances are the folded chain's.
The carrier is not widened. A field that lawfully reaches `κ = 2^(−98)` would need the chart's integer
operator rebased or factored (its decoder and residual kept); that is not exercised by these claims
and is left as an observation at `hnn/chart.rs:422`.

**The defect (c)** [measured]. `hnn::tests::reference::the_carry_passes_each_receptions_end_to_the_next`,
`crates/holonics/src/hnn/tests/reference.rs:822` (`assert_eq!(faces, on)`), on the period-4 chain:
the word a reception's pending ratio reads on fresh charts (`Charts::new()`) differs from the same
word read on the resident's warm charts at window 6 (face 0, cell 0: fibre `4177/2^19` against
`4181/2^19`); the refine equals the warm read at every window and the cold read at all but window 6.
So the saved carry's cold continuation (fresh charts) is not exact where the warm charts have moved:
the lattice word's faces depend on the charts' history. The test stays failing under `#[ignore]`
with the defect named, routed to its owner. The two-class chain does not reach it (and there the
carry moves no read, so it would not test the claim).

## 2a. The defect's cause: the carry is not the whole state the word reads

[measured] On the period-4 chain under `Carry(Nothing)`, over the 14 receptions, the word read on
the resident's **kept charts as saved and read back** (`Charts::write`, `Charts::read`) equals the
refine at every reception. On fresh charts it equals the refine at 13 of 14, and window 6 separates.
At window 6 three operators a deposit moved (`ring 1`, `ring 2`, `contact 1` at conductance carry 0)
keep their charts warm with **no step**, each certificate already within the target. Ring 1's, for
example, is `19/2^31` against the moved operator. The cold start from the scaled transpose reaches
another lattice point in 6 steps (ring 1: `586809557/2^45`). Both are within the target, and they
are different representatives. The faces agree on every grain cell `(carry, phase)` at every
reception. At window 6 the fibres differ (face 0: `4177/2^19` against `4181/2^19`,
`2626/2^19` against `2649/2^19`, `15741/2^18` against `15727/2^18`), and the largest logit
difference is `7/2^17`. From window 7 on the charts still differ but the reads coincide.

[definition; agent-inferred] **The cause** is the test's claim, not the saved state.
- A word is a function of the pending ratio's operands, the published constitution **and the kept
  charts** (`hnn/reference.rs:29`). `chart::refine` keeps a warm chart whose certificate is at most
  `1/2` (`hnn/chart.rs:684`, `:687`) and refines only while it is above the target (`:705`), so after
  a deposit the kept chart is history: a function of its operator only through its certificate
  (`Charts`'s own doc).
- The test read the word on `Charts::new()` (`hnn/tests/reference.rs:822` at `c0275dd0`), and it
  and `Reference::mount_carried`'s doc called the saved carry "the carried state whole". The carry
  is the carried end only. `mount_carried` mounts through `mount_with` on no chart
  (`hnn/reference.rs:1035`, `:1069`).
- The whole state carries the kept charts. The resident's passage writes them
  (`hnn/reference/passage.rs:59`), `mount_continued` restores them (`passage.rs:162`), and a cold
  restore of `Resident::continuing_state` is exact at every reception, window 6 included.
  Dropping them at restore (a mutation at `passage.rs:162`, reverted) separates the restored
  refine at window 6 exactly. So retention holds: the charts are an operand the admitted future
  reads, a probe separates them, and the quotient keeps them.
- Hypothesis (a) of the brief (the charts missing from the continuing state) is refuted by the
  passage.
- Hypothesis (b) names the mechanism (two certified representatives), but comparing at the grain
  is not the law. Two reads each within `1/(2L_R)` of the exact word can straddle a cell, and that
  bound's counterfactual part is owed in #62. The law is exact equality on the kept charts.

[definition; agent-inferred] **The restatement.**
- `the_carry_passes_each_receptions_end_to_the_next` reads the word on the carry and the kept
  charts, each round-tripped through its text, exactly. It counts the fresh-chart read as the probe
  that separates the charts (at least once). Its at-rest comparison reads on the same kept charts,
  so `moved` counts the carry's motion alone.
- The new `a_cold_restore_continues_the_carry_chain_where_the_kept_charts_have_moved` saves the
  whole state before every reception, mounts it cold on a fresh founding constitution and runs
  refine, compare and deposit in lockstep with the uninterrupted resident. Faces, compare,
  deposit, constitution, carry and charts are all equal at all 14 receptions. Before it,
  `a_saved_passage_continues_at_its_epoch_as_the_whole_run` saved at window 4, where the kept
  charts were still the cold ones, and would not have caught a dropped chart.
- `Reference::mount_carried` (and the card's) is documented as the narrower remount, exact only
  where every kept chart is its operator's cold chart.
- `a_collapsed_constitution_remounts_and_reads_alike` states that hypothesis and reads it: every
  chart the remount's word read is the resident's at its key, through the new reading
  `Charts::keys`. The resident also keeps contact 0's chart at conductance carry 0, which that word
  does not read.

[measured] Receipts (`…_receipts/cold-carry/`), at the worktree's own target with a thread budget
of 8, run in sequence because they share the target's lock:
- the diagnostic's per-reception chart readings;
- gate 1, `bash tools/gate.sh`: check, guard lints and guard doctests all ok (10,531, 14,269 and
  17,748 ms), 42,591 ms wall against a 900 s deadline, peak resident set 1,661,176 KiB;
- `cargo test -p holonics --lib`: 1,008 passed, 0 failed, 0 ignored, 235,237 ms wall. It was
  projected at about 350 s from §3's 212,410 ms at 12 threads, so measured over projected is
  `235,237/350,000`, against a 600 s deadline; peak resident set 1,267,848 KiB;
- `cargo test -p holonics --test resident_cold_restore`: 4 passed, 15,478 ms wall against a
  300 s deadline; peak resident set 1,873,320 KiB.

## 3. Gates and receipts

[measured] At this section's commit, the worktree's own target, a thread budget of 12:
- Gate 1, `bash tools/gate.sh`: check, guard lints and guard doctests ok (2,279; 6,683; 17,669 ms;
  26,638 ms wall), the entries' `compile_fail` doctests among them.
- `cargo test -p holonics --lib`: 1,006 passed, 0 failed, 1 ignored (the defect), 212,410 ms of tests
  (217,738 ms wall).
- `cargo test -p holonics --test source_entrance --test resident_cold_restore`: 4 and 4 passed
  (17,910 ms wall with the build); the
  source-entrance assertions unchanged (its fixtures enter through `KnownTruth::cyclic`, the words
  pinned by assertion: `[0, 1]`, the order-2 pair `(2, +1)`).
- The GPU suite, alone on the card under the lock (`flock .local/gpu.lock cargo test -p
  holonics-cuda -- --include-ignored --test-threads=1`): **40 passed, 0 failed**, 364,670 ms of
  tests (365,671 ms wall) against a deadline of 700 s, projected from the partitions measured before
  it (about 370 s: the first run's 36 tests in 180 s, the pump test alone in 155,632 ms, the last
  four in 33,540 ms); measured over projected `365,671/370,000`. The loops before it, each reported
  incomplete or failed and none relaunched with a raised limit: the first full run stopped at its
  180 s deadline on the last test with seven failures, every one in the test migration (the host's
  and the card's words drawn from different seeds; the carry chain's reception counts and campaign
  1's receiving-map shape still the folded fixture's); a subset run stopped at 180 s on the pump
  test, which then ran alone. Receipts: `…_receipts/gpu/`.

The computational object is the helical pair interaction. Of the winding guide's six objects this
loop touches the **helix** (the located step: digit plus carry, at its period's width) and **faces
and placement** (the squares at the consumer; the classes as ports, no residue), with the **pair**
attached through the contacts' quadrance, which decides where the honest fixtures' paths open.

The lessons' failures this loop could repeat, and how each is held: text on its codec's grain (the
byte modes report the refusal; no byte enters); seen graded as unseen (no read touched a final
confirmation seed); a refusal answered with a larger limit (each deadline from measurements, no
rerun with a raised one); bits read as progress (the reproduction is a byte comparison of listings,
not a score).

## 4. Phase 3: the card takes the located digits, a refused step moves nothing, and the capacity is the identity route's

**Adoption.** [measured] Codex's two patches were verified before they were applied. The first is the
device ingest: SHA-256 `1c1197f7…`, 24,369 bytes, on `c2cecc48`, and the four code files' hashes
match its manifest. The second is its invalidation follow-up: SHA-256 `25718f0d…`, 6,593 bytes, with
the CUDA `moment.rs` at `9cdddbab…` before and `8ccc9389…` after, as its manifest states. Both passed
`git apply --check`. Their files are adopted as written, with one fixture change in
`tests/located_ingest.rs`. `Field::declare` refused the fixture's field with `Unreached { ring: 0 }`:
it had no contacts, and its source ring is 2. Two contacts now join the helix's rings on their
common nodes, marked `[agent-inferred, adoption]` in the file. The moment's ingest reads no contact.

The joins:
- the port passes the `Encoded`, or its part, to `open.card.ingest`, and the located refusal is
  removed;
- the `ResidentMoment` fixtures pass the `Encoded` part;
- the layout expectations are rederived from `shared = 12·rings + 8·rings·threads`: 4 rings at
  1,024 threads take `48 + 32·1,024 = 32,816` octets, and 12 rings at 256 threads take
  `144 + 96·256 = 24,720`, under the ceiling 49,144;
- a nonempty located ingest counts its located chart's upload, `8·rings·|A|` octets, beside the
  cells' `4n` and the lift's and phases' `8·(2 + rings)`. The octets are counted once the card has
  launched: on its checked receipt, or on a failure past the launch. A refusal before the launch
  moves nothing across the bus.

**A failed open is discarded.** [definition; agent-inferred] On a refusal the card and the host do
not hold one checked state:
- the card's ingest walks the prefix through the host owner before its launch, so a refused
  occurrence is refused before anything reaches the card;
- after any failure past the launch, the card's moment is invalid until a checked receipt
  (`ResidentMoment::is_valid`, Codex's);
- the host mirror commits the occurrences before the refused one.

So the device port drops the open on every error of its ingest (`port::ingest_open`), and drops any
moment whose re-key fails (`rekey_moments`). The reference port drops a failed open too, so both
ports read the same handles after the same refusal (the parity law). A dropped handle reads
`HnnError::UnknownHandle` (`port_tests::a_failed_ingest_leaves_no_further_reads`). The test's
refusal comes before the card launches, so it tests the port's discard. No test exercises a
failure after the launch, which would invalidate the card's moment: that path needs a driver or
receipt fault, and the tree has no way to inject one.

**A refused occurrence moves nothing.** [definition; agent-inferred] `Field::step_occurrence` takes
the step on a staged copy of the lift and commits it only once the step and, on the located route,
the squares at the consumer hold. `SourceMoment::ingest` counts an occurrence only after its step
returns. The checked squares are the source consumer's, reached through `Field::selective_step`,
`Current::step` and `SourceMoment::ingest`. The keys' candidate-class helpers call the in-crate
`step_class` deliberately, unchecked, as the machine's own crib charts.

[proved-derived] A founded chart rarely refuses. Its transports are shifts of `ℤ/D`, so its reached
span is the union of its openings' orbits under the group its advances generate. That span is all of
`ℤ/D` when the advances generate it, and then no admitted lift leaves it. A step from inside the
span stays inside it, so only a passage's first occurrence can be refused. A refusal therefore needs
two things: advances that do not generate, and a location that is still one gauge class.

[proved-derived] When the index `m` divides the receiving grain `D_low`, the cosets of `mℤ/D` cannot
be told apart. The map `φ(ℓ) = m⌊ℓ/m⌋ + (ℓ + 1 mod m)` keeps every lift in its cell, because a block
of `m` lifts lies within one cell. It commutes with every step by a multiple of `m`, and it carries
each coset to the next. On the helix `(2, 3, 5)` with `m = 3`, one coset's lifts
`r + 3k` read the cells `⌊k/2⌋`: a ten-lift helix `(2, 5)` stepped by `A/3`.

[agent-inferred] That smaller helix sits inside `(2, 3, 5)` in more than one way, which would explain
why index 3 never located in the scans below. Index 5 does not divide `D_low = 6`, and it located.

[measured] The scratch scans behind the fixture (the 200-seed listing is in
`…_receipts/phase3/atomicity_fixture_scan.txt`):

| Advances | Read set | Seeds | One gauge class | Fewest gauge classes |
|---|---|---|---|---|
| multiples of 3 | keys `3j + 1`, `j < 10`, 60 cells | 20 | none | 65 |
| multiples of 3 | keys `k ≢ 0 (mod 3)`, 120 cells | 40 | none | (not kept) |
| multiples of 3 | every key, 60 cells | first 2 | none | 3,186 |
| `5·k`, `k < 6` | every key, 60 cells | 20 | none | 2 |
| `5·(1 + k)`, `k < 5` | every key, 60 cells | 200 (`2_026_100_990 … 2_026_101_189`) | 31 | 2 |

The fixture is the first seed that locates, `2_026_100_995`, with advances `[25, 20, 5, 25, 20]`.
Founded on the first passage's key alone, its chart reaches 6 of the 30 lifts, one coset of
`5ℤ/30`. The test is `hnn::tests::moment::a_refused_located_step_leaves_the_current_and_the_moment_unchanged`:
- from a lift on that coset, the whole passage and a part of it step;
- from the next lift, the first occurrence is refused (`EncodingError::Unreached`, the reading
  square at a lift where the encoding is not founded), and the lift point, the moment and the raw
  lift are unchanged.

Committing the staged lift before the square fails the test, moving the lift from `[0, 0, 1]` to
`[1, 2, 1]`. The same fixture drives the card port's test above.

**The capacity is the identity route's.** [definition; agent-inferred] `N(n)`'s lift factor
`2n + d_g` bounds a ring's ticks by the Boolean fit plus the carry. A located digit steps a ring by
up to `d_g − 1` plus the carry, so the counted `N(n)` certifies nothing on the located route. The
formula is not changed. Its claims (the `hnn::moment` header, `Capacity`, `Field::declare`,
`FieldDeclaration::population`, THE_MACHINE guard 1, the atlas row `hnn.moment-capacity`) are scoped
to the identity route.
- A moment that has counted a located occurrence refuses its capacity, typed
  (`SourceMoment::capacity`, `HnnError::CapacityOwed`), and a later identity-route or empty ingest
  does not downgrade it.
- The ingest receipts and the exposure's state report carry `SourceCapacity`, either `Identity` with
  `⌈log₂N(n)⌉` and `n*`, or `Owed`. Before this change both receipts asserted the identity count for
  every passage. The notebook's identity listing is unchanged.
- The moment's saved line carries an explicit profile, `moment n cursor rings identity|located`. An
  unmarked line is refused (`ContinuingState`, "the moment's route profile"), never read as
  identity. It cannot be told from a located moment saved before the profile, and an old save is a
  superseded prototype (`hnn::tests::moment::the_moment_text_carries_its_route_profile`).

The located route's certificate, with its Lean ranged-clock join, is owed (#62). It is Codex's
follow-up, which takes over `SourceMoment::capacity` and `SourceCapacity`.

**Gates and receipts.** [measured] Every run below read one code tree. The SHA-256 of the tracked code diff plus the
untracked `tests/located_ingest.rs` is `593068e7…` at each run (`…_receipts/phase3/tree.txt`). The
worktree's own target, thread budget 12:
- Gate 1, `bash tools/gate.sh`: check, guard lints and guard doctests ok, 2,238, 6,555 and 17,863 ms (26,660 ms wall), the entries' `compile_fail` doctests among them.
- `cargo test -p holonics --lib`: 1,009 passed, 0 failed, 1 ignored (the defect), 213.51 s of tests (219,304 ms wall). The three new tests are among them: the refused located step, the located moment's capacity, and the route profile.
- `cargo test -p holonics --test source_entrance --test resident_cold_restore`: 4 and 4 passed (17,484 ms wall).
- The card, alone under `.local/gpu.lock`, `--include-ignored --test-threads=1`:
  - the short partition, the four tests measured before at 32,362 ms plus the new port test:
    5 passed, 32,221 ms wall against a deadline of 120 s, so the new test adds nothing measurable;
  - `--test located_ingest`: 1 passed, 1,704 ms wall against a deadline of 60 s, projected from the
    1,785 ms measured before;
  - the full suite: **41 passed, 0 failed**, and `located_ingest` 1 passed; 359.02 s of tests,
    361,011 ms wall, peak resident set 1,013,698,560 bytes. The projection was the last full run's
    378,441 ms, about 380 s, with the deadline fixed at 460 s. Measured over projected:
    `361,011/380,000`.

Receipts: `…_receipts/phase3/`. No limit was raised. Two gate launches of this loop failed before
these runs, and the gates were rerun after each:
- the first did not start, because the host has no `/usr/bin/time`;
- the second hit a compile error in a new test, a local binding that shadowed the support helper
  `encoded`, which was repaired.

The computational object is the helical pair interaction. This loop touches two of the winding
guide's six objects: the **helix** (the card's located step, digit plus carry at `u64`; the coset
structure of a partial span) and **faces and placement** (the squares at the consumer, now
atomic). The **pair** stays attached through the contacts that `located_ingest`'s field needed to
be declared.

The recorded failures this loop could repeat, and how each was held:
- An uncertified deposition step: none. A refused step now commits nothing.
- A located cause carried unrepaired into a new consumer: the capacity formula's identity scope is
  refused, typed, at its consumers, not carried into the located route.
- An authored routine standing in for learning: the fixture's terrain is generated as known truth,
  and the machine meets only its emitted classes.
- A refusal answered with a larger limit: none.
