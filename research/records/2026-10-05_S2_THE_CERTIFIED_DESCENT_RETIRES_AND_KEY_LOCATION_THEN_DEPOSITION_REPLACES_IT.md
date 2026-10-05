# S2: the certified descent retires, and key location then deposition replaces it

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** B and E of U6 (THE_REBUILD, "U6's
order from October 5"): the library spine's S2 row, "`hnn::executed`'s own move … retires once B's
acceptance reads, replaced by key location then deposition". **Grade.** [measured] for the counts
of §1 and §5 (the retirement commit `2636aaa7` against `9078f103`); [definition] for the laws restated in §2,
each with its first owner; [agent-inferred] for what was kept and what was retired.

**Occasion.** B's acceptance has read. With its key located by loop closure (16 observations against
`n*_terrain = 7`) and deposited by one certified step, order-2 releases 128 of 128 sections whole on
its final confirmation, read once
([the pair release](2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL.md), "The final
confirmation, read once"); the line 128 of 128 on its own
([the regressions](2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE.md)
§7.1); the alternation 46 of 46 nonconstant on validation once the gain read the joined bank
([the pair gain](2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT.md), #365). The
learner it replaces, the certified descent of the release's own comparison (`hnn::executed`), read
1,024 observations on order-2 and never locked it
([the two counts](2026-09-30_THE_TWO_COUNTS_MEASURED_THE_TERRAIN_PINS_ORDER_TWO_IN_SEVEN_READINGS_AND_THE_CERTIFIED_STEP_DESCENDS_TOWARD_TIES_WHILE_ITS_DECISIONS_STAY_AT_A_GUESS.md));
a strictly monotone descent cannot cross a sheet's flip, which costs `34037/4096` nats
([the refit's ingredients](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)
§9). Its harness, loop 1c's launcher, failed at `9078f103` (3 of its example's 10 tests and 13
launcher tests: gate A's saved state refused at the chart's scale), a superseded line's failure.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this consolidation touches
**the pair** (the located pair contact is what stays: its slip, its deposit, the release's reading
of it) and keeps the helix, faces and placement, the cell holonomy, the tube and the tower thread
attached and unchanged: no law of any of them moves.

## 0. The recorded failures this could repeat, and how each was held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and
the [prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):
- **Lesson 3 and failure 4, a located cause carried into a new consumer.** The descent's measured
  cause (a monotone step cannot cross a flip) is not carried: no kept consumer reads the
  comparison, its covector or its ladder. The located pair's deposit keeps the one law it shared
  with the move, the library's certified step (`holon::deposition::CertifiedStep`), at the loci the
  key reaches only.
- **Failure 5, an uncertified deposition.** The kept deposit is unchanged: adopted only when
  `CertifiedStep::holds`, the slip falls by the certified decrease and every entry stays within
  `2³`.
- **"Unconsumed Rust is deleted once any law that only it states has moved"** (CLAUDE.md). Every
  law the retired code stated is in Lean, in an atlas row with its record, or restated in §2 below
  before the code was deleted.
- **Failure 9, a refusal answered with a larger limit.** No run was relaunched; the tests ran
  inside their projected deadlines (§5).

## 1. What retired

| Retired | Lines at `9078f103` | Kept |
|---|---|---|
| `crates/holonics/src/hnn/executed.rs`: the comparison (`Predicate`, `Context`, `Request`, `Composition`, `Reading`, `Comparison`, `StationComparison`, `OrderReading`, `Excess`, `TermSite`, `TermReading`, `RequestComparison`, `TermCounts`, `BatchComparison`, `lock_face`, `LockFace`, `compare`, `sites_of`, `OrderSheet`, `OrderTerm`, `GapEnd`), its proposal and first-order certificate (`TermKind`, `SlopeSplit`, `modulus_slopes`, `SiteGradient`, `site_gradients`, `frozen_reread`, `FirstOrderReading`), the move (`TrialRefusal`, `Trial`, `MoveRefusal`, `LadderStart`, `MoveMetric`, `ladder_start`, `Persistence`, `ExecutedMove`, `Reread`, `ReleaseExcursion`, `Schedule`, `MoveMargins`, `move_margins`, `executed_move`, `executed_move_in`, `executed_move_guarded`, `executed_move_scheduled`), the run (`RunEnd`, `ReleaseRun`, `release_run`), the metrics (`DirectionReading`, `unit_direction`, `PlaneTerm`, `WitnessForm`, `witness_form`, `PlaneReading`, `witness_plane`, `witness_plane_along`, `SpanReading`, `witness_span`, `KineticStop`, `KineticSolve`, `ModulusCoupling`, `KineticReading`, `kinetic_reading`), the receipts (`PairingReading`, `pairing_receipt`), the comparison's typed refusal of a closed pair contact, `ENTRY_BOUND` and the test probes | 6,012 → 295 | `pair_deposit`, `PairDeposit`, `pair_slip`, `entry_bound`, `ln_two` |
| `crates/holonics/src/hnn/tests/lock_face.rs`, `tests/coupling.rs` (31 and 4 tests) | 1,789 + 277 | the three continuing-state tests, rewritten on a located pair's deposit, in `tests/executed.rs` |
| `tests/executed.rs`'s predicate and excursion tests; `tests/prediction.rs`'s five comparison and move tests, the closed-contact refusal, `executed_requests` and `joint_bank` | 2 + 6 tests | the ring's covector tests, the pair deposit's tests, the pair release's tests |
| `research/notebook/hnn_design/hnn_executed_loop.rs`'s 25 descent modes, the partial remount of `E` and `ρ`, the manifest of states written before the identity and its `sha2` dev-dependency | 4,903 → 852 | `evaluate`, `counts`, `cell`, `terrain_pairs`, `write_state`, `mount` (a complete state, whole), `founded_opening` |
| `hnn_loop_1c.rs` (its 10 tests), `loop_1c_runs.sh`, `loop_1c_runs_tests.sh`, `read_probe.sh`, `replay_baseline.sh` | 2,625 + 481 + 405 + 50 + 72 | `hnn_prediction.rs`'s dispatch of `evaluate`, `counts`, `keys`, `keys-probe`, `pair-members`, `text`, `text-repair`, `repair` (662 → 383) |
| `research/runs/loop-1c/` (11 pins), `research/runs/guards/{train,coupling}-dev.pin`, `research/runs/u6/` (the chains, the queues, 23 states, the manifest), `research/runs/branch-archive/` (358 files: the run branches' states, #275) | 78,139 | `research/runs/guards/{text,text-repair}-dev.pin` |

Every retired file is at
[`9078f103`](https://github.com/brandonrdug/holonics/tree/9078f103); the notebook's
[retired harnesses](../notebook/hnn_design/README.md#the-retired-harnesses) name each with its
source. The baseline replay is retired with the descent's states it replayed: at `9078f103` it could
not match (the release's line names its closed contacts, which its reference predates, and its
trained port, a bare `E` and `ρ`, mounts only as `partial:`).

## 2. The laws the retired code stated, and where each lives

Every expression keeps its atlas row; a retired Rust owner became
`H:crates/holonics/src/hnn/executed.rs@9078f103` in the same commit (17 rows of `objects.tsv`).

| Law | Lean | Atlas; record |
|---|---|---|
| the simple root's eigen-derivative and the monodromy's variation (the Rust owner `hnn::ring` stays) | `HNN/ExecutedComparison.{simple_root_deriv, log_modulus_deriv, product_deriv}` | `hnn.executed-growth-covector`, `hnn.monodromy-variation` |
| the station's predicates, sufficient for order and section; the decisions along the key-consistent prefix | `predicates_release_the_section`, `decisions_release_the_section` | `hnn.release-comparison`, `hnn.lock-face-comparison`; [the diagnosis](2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md) §5 |
| the hinge's zero set | `hinge_zero_iff`, `hinge_zero_at_tie`, `hinge_right_leaves` | `hnn.hinge-zero-set` |
| the lock face, its solved level, its covector `θ − q` and first-order certificate | `lockFace_*`, `sum_upper_dini_descends` | `hnn.lock-face-comparison`, `hnn.lock-face-periods`; [step 1b's pin](2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md) §2, §13 |
| a max and a sum of maxes descend; disjoint enclosures certify a strict decrease; the modulus's least-squares step | `max_descends`, `sum_max_descends`, `disjoint_enclosures_decrease`, `modulus_least_squares` | `hnn.executed-move` |
| the release's guard, the excursion and the run's close at any length; the halvings end at the lattice | `HNN/ExecutedComparison.{own_telescopes, checkpoint_one_iff, excursion_enclosure, …}`, `HNN/ReleaseRun` | `hnn.release-guard`, `hnn.release-run`; [the run-end record](2026-10-02_A_RUN_CLOSES_ON_A_CONDITION_NOT_A_LENGTH_AND_THE_HALVINGS_END_AT_THE_LATTICE.md) |
| the certified lock and the order term's two ends (the Rust owner `prediction::uncertified_largest` stays) | `certifiedLock_*`, `order_solved_locks_no_wrong` | `hnn.certified-lock` |
| the move's metric: its reach, the reading metric, the port's hidden mass, the witness's Fisher form on the move's plane | `metric_step_zero_iff`, `posDef_reach`, `readingMetric_*`, `hidden_never_native`, … | `hnn.move-reach`, `hnn.reading-metric`, `hnn.port-mass-hidden`, `hnn.witness-plane`; [the witness's metric](2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md) |
| the receiver's minimum-energy move and the joined modulus | `Holon/Element:KineticFace.unique_minimum_energy` | `hnn.kinetic-move`, `hnn.kinetic-modulus`; [the representation](2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md), [the joined move](2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md) |
| the excess's piecewise derivative and the ladder's start | owed (#62) | `hnn.excess-ladder-start`; step 1b's pin §13.5; restated below |
| each decision term's pullback, the frozen re-read; a partition's reading | `lockFace_covector`; `HNN/Prediction.partition_reading_ignores_compared_targets` | `hnn.site-gradient`, `hnn.partition-comparison`; [loop 1c's pin](2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md) |
| the restore law (the Rust owner `hnn::constitution::ContinuingState` stays, its tests kept) | `restoreStanding`, `restored_continuation_agrees`, `equal_states_agree` | `hnn.restore-standing` |

Three statements stood only in the Rust and are restated here [definition, as their owner stated
them at `9078f103`]:
1. **The ladder's start.** From the excess's lower end `X⁻`, the upper end `s_X⁺` of its piecewise
   directional derivative on the joint unit move, and the unit move's largest entry change `u`:
   `η₀ = 2^⌊log₂ min(X⁻/(−s_X⁺), ½/u)⌋` when `X⁻ > 0` and `s_X⁺ < 0`; the entry scale `½/u` alone
   otherwise (`1` when `u = 0`), so neither a zero excess nor a nonnegative slope enters a division.
   Each trial `η₀ 2^(−k)` is adopted only when every condition of adoption holds on the carried
   successor (the entry bound, the first-order certificate negative on the carried move, every
   crossing admissible and lock certified, the fixed incumbent mask's composition and the
   successor's own release's composition both strictly lower by disjoint enclosures), and the
   halvings end when `η · 2u` falls below the source port's lattice unit.
2. **The kinetic solve's recurrence.** Conjugate gradients on `AᵀFA v = −Aᵀc`, preconditioned by
   `M⁻¹`, `M = I ⊗ H′`, from `v = 0`, so that every iterate is `v_k = M⁻¹Aᵀμ_k`: a deposition of the
   returns with reading weights `−μ_k`, its first iterate the normal law's own direction
   `−M⁻¹Aᵀc`. It stops when the residual's energy falls to `2^(−32)` of its opening, at a direction
   the readings do not see (`pᵀAᵀFAp ≤ 0`, the kernel), or after as many iterations as reading
   coordinates. With the modulus joined, one Schur complement: `x_ρ = (y_ρ − ⟨bH′⁻¹, Y⟩)/s`,
   `X = YH′⁻¹ − x_ρ bH′⁻¹`, `s = g − ⟨b, bH′⁻¹⟩`, the modulus joined only where `s > 0`.
3. **The persistence reads.** Of the incumbent's locks solved at their refinement (the rational
   test) with a later lock in their section, each re-read with every later lock placed: it stays
   solved, or it falls, split into `reversed` (the strict test proved to fail) and `uncertified`
   (undecided on the enclosures, a lost certification and not a proved reversal).

These are laws of a retired learner. None is ported: a later loop that needs one reads it here or at
`9078f103`, and recovers it before rebuilding it.

## 3. What stays, and its consumers

- `hnn::executed::pair_deposit` (lane B's deposit; consumers `hnn_keys_loop.rs`'s `keys` and the
  pair release's tests) and `pair_slip` (consumer `hnn::prediction::closed_pairs`, lane C's
  release). The module's header now states that it owns the located pair's deposit and names the
  retired comparison and move with their commit.
- `hnn::executed::ln_two` (consumers `hnn::reference::refining_grain_exponent` and
  `hnn::constitution`'s receiving prior) and `entry_bound` (the deposit's condition of adoption).
- The harness's `evaluate` (every Oct 5 record's release reads), `counts` (`n*_terrain`, the
  yardstick of the readings to lock) and their helpers; `mount` reads a complete continuing state
  whole, which every kept state is (each carries its material identity and check).
- The constitution's continuing state keeps its tests: a restored checkpoint continues exactly over
  successive deposits; it refuses foreign material and damage; it carries the reception's end
  inside its check. They read the state through a located pair's deposit instead of the move.

## 4. Residue at other lanes' owners [measured]

Code that only the retired learner consumed, in files this lane does not edit; each is named for
its owner's next change:
- `hnn/mod.rs:83–87` and `:131` (the module list and the law table) still describe `executed` as
  the comparison and its move; `HnnError::{WindowDecrease, ExcursionHeight}` (`hnn/mod.rs`) have no
  producer.
- `hnn/ring.rs:2157` links `crate::hnn::executed::lock_face` (a broken intra-doc link); the
  covector owners `ReceivingBank::{read_turn_covector, turn_variation, directional_routes}`,
  `TurnCovector`, `MemberCovector` and `CovectorRefusal` have no library consumer (their tests in
  `tests/executed.rs` stay).
- `hnn/constitution.rs:4341` names `hnn::executed::executed_move` in `stepped_source`'s doc (its
  consumer is now `pair_deposit`); `ContinuingState::stamped` has no notebook consumer (the
  manifest of earlier states is retired; its test stays).
- `hnn/prediction.rs` (lane C's owner, its code unchanged here, its docs repinned): `bank_release`'s
  genericity over `JointGrowth` (`impl JointGrowth for TurnCovector`), `BankRefinement` and `keep`,
  `bank_release_ordered` with `LockOrder::{Ascending, Descending}`, `bank_release_forced` and the
  iteration's forced targets, `mask`, and `BankPlacement::{storage_over, modulus_derivative,
  reach_slopes, reach_derivative, exact_storage}` have no consumer outside the release and its
  tests.
- `hnn/constitution.rs` (`Constitution::material_identity`, `continued`): every complete state
  written before #367, the October 5 keys states included, is refused at `9078f103` as another
  opening's material (§5), so no committed keys state mounts until the states are written again or
  the identity stops reading the constitution's printed layout.
- Lean: `HNN.lean:103–104`, `HNN/ExecutedComparison.lean:45, 404, 1443, 2174`,
  `HNN/ReleaseRun.lean:14`, `HNN/BankFace.lean:19` and `HolonicsResearch/HNN/OrderTemperature.lean:390`
  name the retired Rust owners in comments. They are repinned at the next Lean change of those
  files: `HNN.lean` is imported through `Framework` by 62 modules, so a comment there rebuilds them.

## 5. Gates and time

Thread budget 12 (`cargo -j 12`, `--test-threads=12`), the worktree's own target. The library
tests' projection was the baseline's measured wall time, its deadline the outer `timeout` of
1,500,000 ms; nothing was relaunched.

| Gate | Before (`9078f103`) | After | Wall ms |
|---|---|---|---|
| `cargo test -p holonics --lib` | 1034 passed, 0 failed (292,770 ms of tests) | 994 passed, 0 failed (163,910 ms of tests) | 322,707 before; 169,841 after (ratio `169841/322707`) |
| `bash tools/gate.sh` (check, guard lints, guard doctests) | — | ok, ok, ok (33 doctests) | 13,542 |
| `cargo test -p holonics --example hnn_prediction` | 10 tests, 3 failing (loop 1c's) | 0 tests: the example builds | 16,766 |
| `loop_1c_runs_tests.sh` | 13 failing | retired | — |
| `cargo check -p holonics-cuda --all-targets` | — | ok | 1,330 (cached) |

The library tests changed by exactly the retired and moved tests: 31 and 4 tests of
`lock_face.rs` and `coupling.rs`, 2 of `tests/executed.rs` and 6 of `tests/prediction.rs` gone, and
the three continuing-state tests added under their new names (`1034 − 43 + 3 = 994`). The three
take a deposit in place of a move; ten of the retired tests had each run past 60,000 ms.

**The kept release path, read again** [measured]. The pair gain record's development reads
(`executed evaluate <terrain> 2026093042 8` over the keys states, each terrain) were rerun on this
change's release build (31,495 ms). Each refused before its first request (243, 239 and 239 ms, exit
101): `Constitution::continued` refuses lane B's and the regressions' states as "the state continues
another opening's material". The same read at `9078f103`, built in a detached worktree (70,861 ms),
refuses identically, so the refusal predates this change: a state's material identity is the residue
of the blanked opening's printed form, and the constitution's layout moved after the states were
written: the one change to `hnn/constitution.rs` after #365's read of them is #367 (lane A's quartic
gain, `6a251c38`). The states are written again by `executed keys` at the current layout, or the
identity is read from the declared material rather than from its printed form; it is lane A's and
the constitution's owner's subject, named in §4.

Receipts: [`2026-10-05_S2_THE_CERTIFIED_DESCENT_RETIRES_receipts/`](2026-10-05_S2_THE_CERTIFIED_DESCENT_RETIRES_receipts/)
(the library tests' results and the retired and added test names, the gates, the replay script and
its refusals, the control read at `9078f103`). No Lean changed (§4 names the comments owed); no card
run: no kernel or card path changed.
