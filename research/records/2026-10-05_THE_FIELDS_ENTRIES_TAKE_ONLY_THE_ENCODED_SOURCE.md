# The field's entries take only the encoded source, and the folded fixtures are re-derived

**Date.** October 5. **Issues.** #73, #148, #76, #63. **Lane.** E of U6, phase 2 (the boundary's
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

**The card.** Its port accepts `Encoded` and refuses a located route's passage (`Unadmitted`): the
`hnn_moment_ingest` kernel steps by the lock's fit alone. The kernel taking `digits(A) + carry` is
device debt for #76 (Codex, branched off `c2cecc48`).

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
| `reference::the_carry_passes_each_receptions_end_to_the_next` | (c) | Defect, below. |

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
