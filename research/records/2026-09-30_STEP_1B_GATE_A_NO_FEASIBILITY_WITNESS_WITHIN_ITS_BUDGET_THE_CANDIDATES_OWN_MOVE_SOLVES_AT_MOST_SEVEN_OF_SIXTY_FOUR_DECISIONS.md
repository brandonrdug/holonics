# Step 1b, gate A: the candidate built with its guards and its continuing state, and no feasibility witness within its budget; the candidate's own move solves at most seven of sixty-four decisions

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6, step 1, loop 1b, gate A);
#62. **Grade.** [definition; agent-inferred] for the build and the witness's procedure;
[measured] for the tests, the timing, the witness, the replay and the gates;
[proved-derived; formal-checked] only where a cited Lean theorem holds it; owed (#62) as stated in §7.

**Occasion.** The [pin](2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md),
amended after GPT-6 Astra's review (§13), stages 1b's work: gate A builds the candidate and its
contract, tests it, and exhibits (or fails to exhibit) a constrained feasibility witness before any
long run; gates B and C open only after A is decided. This record is gate A's receipt. Gate B and
gate C were not run; the final confirmation seeds were not read.

The computational object is the helical pair interaction, read through the complex parametron's
executed comparison; of the [winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s objects
this touches faces and placement (each station's lock read whole at the section the release
placed) and the cell holonomy (the executed growth over one turn); the helix, the pair, the tube and
the tower thread stay attached and unchanged.

## 0. The failures this work could repeat, and what held each off

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and
the [prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):

- **An uncertified step**: every guard stays a commit guard. The two repairs refuse where 1a's move
  let a term through (an unresolved active member) or refused too early (the port's slope alone);
  the joint direction's modulus part, enclosed for cost, keeps its rounding charged.
- **A local pass read as progress**: the descent account is the fixed mask's; the successor's own
  release's score and the context change are printed beside it and never read as decision progress
  (the development move below shows the mask falling while the own score rose).
- **Seen material graded as unseen**: development seeds only (`2_026_093_061` for the witness,
  `2_026_093_062` for timing); no training, validation or final seed was read.
- **A refusal answered with a larger limit**: the first timing move reached its guard and was
  reported incomplete; its cause was located and repaired in the owner (an exact product of
  thousands of bits), and the next timing was a fresh measurement on the same declared move, not a
  rerun at a larger limit. The witness's budget was pinned before its run and not raised.
- **An authored routine standing in for learning**: the witness is the candidate's own certified
  move on its own readings; no key family, survivor, lag or answer reaches the receiver, the update
  or the release (the counts mode is untouched and uncalled).

## 1. What was built [definition; agent-inferred]

The owners, at `c48c864f` (the build) and `d8cc9298` (its cost repair, §4.1), on main's `21c98f85`:

- **`hnn::executed`, the declared comparison** (`Comparison { composition, reading }`):
  - `Composition::Hinge` (1a's `F = Σ (f)_+`) and `Composition::LockFace` (`L = Σ ℓ`,
    `ℓ = log((1 + Σ a)/a_t)`), each with its solved level (zero; `log 2`) and its excess
    `X = Σ (term − level)_+`;
  - `Reading::Every` (1a's), `Reading::Decisions` (§2.4: `d(j)` the refinement locking `j` when
    that is before `r*`, else `r*`) and `Reading::TeacherForced` (the diagnostic), read by one pure
    function of the release's refinements (`sites_of`);
  - `lock_face` on exact enclosures: `ℓ ∈ [ln(1 + (1 + Σ_(x≠t) L_x)/U_t), ln(1 + (1 + Σ_(x≠t) U_x)/L_t)]`,
    the strict rational solved test `1 + Σ_(x≠t) U_x < L_t` (holds; fails at `1 + Σ_(x≠t) L_x ≥ U_t`;
    else undecided), authoritative over the logarithm's enclosure; `θ_x` enclosed; the excess exactly
    zero where the test holds. Every station comparison (`StationComparison`) carries the hinge's
    `f`, the lock face's `ℓ`, the solved predicate, `θ_t` and the ranks (the target among the five
    and among the four symbols, the termination among the five).
- **The proposal and the certificate**: the hinge as before (its leading branch at `±1`; its active
  branches' members in the certificate); the lock face at `θ_x` and `θ_t − 1` on every candidate's
  leading member (the dyadic face of each enclosure's midpoint), its certificate
  `Σ_(x≠t) sup(θ_x · D_x) + sup((θ_t − 1) · D_t)` over each candidate's enclosure-active members, in
  interval arithmetic over the shares' enclosures (`lock_term_bound`). `returns`, the source port's
  normal law and the modulus's least-squares step are unchanged in law, the sign generalized to the
  contribution's weight.
- **The two repaired guards, in the shared move for every arm** (§13.4):
  - `certificate_refusal`: a term of the certificate's support with an unresolved active member
    refuses the move, typed (`MoveRefusal::Unresolved(n)`), before any trial; it is never bounded by
    its resolved members alone. The hinge reads its target's and its active rivals' members; the
    lock face reads every candidate's.
  - `slope_refusal`: the slope is read on the joint unit direction, each storage move the exact
    `E`-part plus `(∂z/∂ρ)Δρ` at the modulus's least-squares unit move, the latter enclosed outward
    on dyadics of 128 significant bits (`JOINT_BITS`, `d8cc9298`: the exact product cost minutes a
    batch, §4.1), before any refusal; the port's part alone is a receipt
    (`ExecutedMove::port_slope`).
  - The targets are validated (one per station, each a class of the chart; a partition's mask one
    flag per station) before anything is read.
- **The two readings** (§13.1): the fixed incumbent mask (the incumbent's terms' sections, held
  within the move and dropped with it) carries the descent account: each trial re-reads exactly
  those sections at the successor, taking a reading from the successor's own release where it
  executed the same section (the same function, the same value), and adopts only on
  `C_mask(Θ′)⁺ < C(Θ)⁻`. The successor's own release is read beside it for its guards (admission,
  every lock's Floquet certificate, support) and its behaviour; `Trial::change` is the own reading
  less the mask's, enclosed.
- **The ladder's start** (§13.5, `ladder_start`): `η₀ = 2^⌊log₂ min(X⁻/(−s_X⁺), ½/u)⌋` with `s_X`
  the excess's piecewise bound on the joint unit move (`FirstOrderReading::excess`: the bounds of the
  terms above their level, `max(bound, 0)` over the boundary terms, nothing from solved ones); the
  entry scale `½/u` alone at `X⁻ = 0` (`LadderStart::ExcessZero`) or `s_X⁺ ≥ 0`
  (`ExcessRising`); `1` in place of `½/u` at `u = 0`.
- **The counts and the persistence reads**: `TermCounts` (obligations, attempted, coverage,
  absent, post-error, held, support, solved, boundary, above) on every reading; `Persistence` (each
  lock, whether its lock face was solved at its refinement, and each solved lock with a later lock
  re-read with every other lock of its release placed: stays or falls).
- **`hnn::constitution::ContinuingState`** (§13.6): the source port's normal law whole (`E`, the
  carried Gram, the solved chart's lattice, support, block and certificate, the remainders of `W` and
  `H`), `ρ`, the source port's clock, the commit and the storage product;
  `Constitution::continuing_state` (refused, typed, where another locus moved, a locus is released or
  a factor family carries a remainder), `Constitution::continued` (onto the declared opening only)
  and an exact text whose first lines are the partial remount's form (`E rows cols`, the rows,
  `rho ρ`).
- **The harness** (`hnn_executed_loop.rs`, `hnn_prediction.rs`): `executed train`'s arms
  `<hinge|lock>-<all|dec|tf|partition>` (`lock-dec`, `lock-all`, `hinge-dec`, `hinge-all`,
  `lock-tf`), openings `@ρ` and `~<checkpoint>` (a full remount); D1 (the composition, `X`, the
  joint, port and excess slopes, the ladder's start and its kind, every trial with its readings, the
  mask's measured descent beside the own release and the context change, I4 at the open section
  and at the release's locks, the counts, the persistence reads), D2 (three scopes: every
  refinement, the open section, the declared reading's terms; the solved count and `θ_t` per
  stratum), I7 (the ranks); checkpoints and the running `out` written as the complete continuing
  state; a remount of `E` and `ρ` alone labelled partial on stderr wherever one is read (stdout
  untouched, so the replay's listing is the same); `executed witness` (gate A's) and
  `executed causal` (I6). Not run here: gate B's arms.
- **The atlas**: `hnn.lock-face-comparison` and `hnn.executed-move` gain their Rust owners and
  laws; `hnn.release-comparison` gains the solved test and the readings; new rows
  `hnn.continuing-state` and `hnn.excess-ladder-start`.

## 2. The tests and their results [measured]

`hnn::tests::lock_face`, eleven tests (`crates/holonics/src/hnn/tests/lock_face.rs`), all pass
(`cargo test -p holonics --lib`: 882 passed, 0 failed, at `d8cc9298`; 871 at `21c98f85`, the eleven
added). The five existing tests of the executed comparison and its move in `hnn::tests::prediction`
read 1a's comparison (`Comparison::HINGE_EVERY`) and pass under the repaired guards; their two
adoption assertions now read the fixed mask's value, and the receipts test reads each term's kind
from the incumbent's terms:

| Test | What it holds |
|---|---|
| `the_lock_face_reads_the_lock_whole_against_its_resting_sheet` | at the flip exactly (`a_t = 3`, four rivals `1/2`) `ℓ` encloses `ln 2`, the station fails the solved test, is a boundary term with excess lower end `0`; the shares are `1/2` and `1/12` and with the resting sheet's `1/6` sum to one; past the flip (`a_t = 4`) the test holds, the excess is exactly `0` and `ℓ⁺ < ln 2⁻`; at `a_t = 3` against `1, 1, 1/2, 1/2` the release's class and threshold hold while the solved test fails (strictly stronger); a target at the unit with vanishing rivals is never solved (the resting sheet is the threshold); a tie of five at `2` reads `ℓ⁻ > ln 5⁺`, above the level, where the hinge's `f` straddles zero and the class fails; overlapping enclosures leave the test undecided |
| `a_zero_or_unsupported_target_is_refused_typed` | a target with lower end `0` refuses the face (`NonpositiveDeclaration`), a zero rival is read, a target outside the candidates refuses (`Shape`), a negative enclosure refuses; on every arm, a short target list (`Shape`), a target `3` of three classes (`CellOutside`) and a partition mask of the wrong length (`Shape`) refuse before anything is read |
| `the_ladder_starts_from_the_excess_and_never_divides_by_zero` | `ladder_start` at `u = 1/4`: `X⁻ = 0` gives `2` (`ExcessZero`); `s_X⁺ = 0` and `s_X⁺ = 3` give `2` (`ExcessRising`); `X⁻ = 1/8, s_X⁺ = −1` gives `1/8` and `X⁻ = 3/16` gives `1/8` (`FirstOrderZero`); `X⁻ = 3, s_X⁺ = −1/2` gives `2` (`EntryScale`); `u = 0` gives `1`; a station at exactly `ln 2` beside a solved one sums to `X⁻ = 0`, the entry scale, and stays unsolved |
| `an_unresolved_active_member_refuses_every_composition` | on synthetic covectors (a target below threshold, an active rival at `1`, an inactive rival at `1/4`): an unresolved member of the target or of the active rival refuses both compositions (`Unresolved(1)`, the first order counting it); one of the inactive rival refuses the lock face (every candidate read) and not the hinge (its certificate does not read that branch) |
| `the_slope_is_read_on_the_joint_direction` | a lock-face term above its level (every reading `1`, `θ = 1/4`): the port's moves (rivals `+1`) bound `1/2 ≥ 0` and refuse alone (`NoDescent`); joined by the modulus's (target `+2`) the joint bound is exactly `−1` and passes, the ladder starting at `1/2` from the excess's first-order zero; the weights are `θ_x = 1/4` and `θ_t − 1 = −3/4` |
| `active_face_ties_are_read_by_every_active_member` | a lock-face term with two active target members (`+1`, `−1`) and two rival members (`−2`, `+3`) is bounded by exactly `3/2` (the rival's largest, the target's least); a hinge term whose two rivals tie with its threshold is bounded by exactly `1`, its largest branch |
| `the_decisions_read_each_station_once_along_the_consistent_prefix` | synthetic refinements: on a release with a wrong lock at refinement 1, `r* = 1`, sites `(1, 0)`, `(1, 1)` held, `(0, 2)`, `(1, 3)` held, none post-error; every refinement's reading marks refinement 2's two sites post-error; the teacher-forced sections place the earlier targets, at refinement 0 only where the release executed it; a hold reads all four at refinement 0, held; a refused certificate at refinement 1 reads three held stations there and station 2 at 0; a partition reads its open stations |
| `the_fixed_mask_rereads_the_incumbents_sections` | on every arm, the mask re-read at the incumbent gives the comparison's value and excess exactly, and the own reading is the comparison |
| `a_hold_keeps_every_station_obligation` | at `E = 0` every release holds at the open section; every arm covers the 8 obligations, none absent; the decisions and teacher-forced readings attempt 8, the decisions 8 held and none post-error |
| `the_guards_hold_symmetrically_on_every_arm` | the five arms on the joint field's two requests: each adopted move has no unresolved term, a negative joint slope, its first trial at the stated start, the mask's value strictly below the incumbent's by disjoint enclosures (and equal to the mask re-read at the successor), its first order negative, its entries within the bound, every lock of its own release certified, one commit; each refusal is typed and consistent; the port's slope equals the joint where the modulus does not move; obligations covered; persistence consistent; the candidate arm adopted |
| `a_restored_checkpoint_continues_exactly_over_successive_receptions` | from the joint field's opening at `ρ = 3/4`, one adopted move of the candidate arm, the state written as text and read back equals the state, and restored onto the opening equals the continued constitution; over three further receptions the restored and the continued return equal comparisons, equal returns at `E`, equal trials (steps, moduli, first orders, mask values, own readings, refusals, terms' bounds, carried source steps), equal adoption, equal clocks and equal successors (three adopted); the partial text (`E` and `rho` alone) is refused as a continuing state, the partial remount differs from the continued constitution in its Gram, and its next move reads the same release and adopts a different successor; a checkpoint restored onto a constitution that is not the declared opening is refused |

On the joint field (period 6, 4 stations, 3 classes; two requests), the five arms each adopted their
first trial (the diagnostic run of the guard test, not kept as a test assertion except for the
candidate arm): the lock face at the decisions at `1/8` (`FirstOrderZero`), at every refinement at
`1/2` (`EntryScale`), teacher-forced at `1/8`; the hinge at the decisions at `1/128`, at every
refinement at `1/64` (`FirstOrderZero`); no unresolved member; at every refinement 20 terms with 6
post-error and 13 held, at the decisions 8 with 4 held and none post-error.

## 3. The boundary cases and their behaviours [definition; agent-inferred; tested]

| Case | Behaviour |
|---|---|
| `X = 0` with stations at exactly `ℓ = ln 2` unsolved | the station's solved test fails (`1 + Σ L_x ≥ U_t` with equality), it is a boundary term, its excess has lower end `0`; `X⁻ = 0` starts the ladder at the entry scale (`ExcessZero`), no division; nothing is counted solved by it; the move proceeds under every guard, the composition `L` still descending |
| `X > 0` with `s_X⁺ ≥ 0` (nonnegative derivative) | the excess's linearization reaches no zero: the entry scale alone (`ExcessRising`); the move's own guard reads the composition's joint slope, which must be negative or the move is refused (`NoDescent`) |
| `X > 0` with an unresolved `D X` (an unresolved active member) | the move is refused before any trial (`MoveRefusal::Unresolved(n)`): the derivative is not formed and no trial can be adopted |
| active-face ties (several members of a candidate reaching its joint's lower end; rival branches tied with the threshold) | every active member is read: the lock face's `D_x` spans their least lower and largest upper pairing, rivals by the largest, the target by the least; the hinge takes its largest active branch |
| candidate ties (a rival at the target's reading) | the lock face reads `ℓ ≥ ln 2`, above its level where the rest exceeds the target (a tie of five at `a ≥ 1` reads `ln(5 + 1/a)`); the hinge's `f` straddles zero there, a boundary term hinged at zero |
| a zero target (lower end not positive) | refused, typed: at the incumbent the comparison's `HnnError::NonpositiveDeclaration` (the move is not formed), at a successor `TrialRefusal::Unsupported` (the trial refused); never solved, never divided by |
| an unsupported target (outside the chart, or a missing or extra target, or a partition mask of the wrong length) | refused before reading (`CellOutside`, `Shape`) on every arm |
| a hold or a refused certificate | the decisions reading keeps every station's obligation, read at `r*` and marked held; no station is absent |

## 4. The timing and the witness [measured]

### 4.1 The development move, for the projection (seed `2_026_093_062`, 8 requests)

- **The first timing move did not finish** within its 1,800,000 ms guard (incomplete: 5,838,280
  ms of CPU, at 327 of 2,400 percent, mostly serial). Profiled on two of its requests (a temporary
  instrumentation, not committed): the incumbent's reading 16,690 ms, the port's first order 384
  ms, the joint direction's first order 180,662 ms. The exact product of the transported weights'
  derivatives with the modulus's least-squares unit move carries thousands of bits a coordinate,
  and every pairing of the certificate summed them. Repaired in the owner (`d8cc9298`: the modulus
  part enclosed at 128 bits, the term bounds and the placements on the host's cores): on the two
  requests the joint first order then took 3,398 ms and the move 63,141 ms.
- **After the repair** the move took 164,736 ms (1,204 of 2,400 percent; resident 196,288,512
  bytes at its peak). At the founded opening: `L ∈ [477639/4096, 477645/4096)` nats,
  `X ∈ [297681/4096, 297686/4096)`, 4 of 64 decision terms solved, 51 held, none post-error, no
  unresolved member. The ladder started at `1/2` (the excess's first-order zero, under the entry
  scale `[62602/65536, 62603/65536)`); `η = 1/2` was refused (`NotBelow`: the mask's `L` rose to
  `[502893/4096, 502898/4096)`); `η = 1/4` was adopted, the mask's `L` falling to
  `[441257/4096, 441263/4096)` (measured descent `[36377/4096, 36387/4096)` against the
  certificate's first-order prediction `[97569/4096, 97572/4096)`). The successor's own release read
  `L_own ∈ [480584/4096, 480589/4096)`, above the incumbent's: the context change was
  `[39322/4096, 39332/4096)`. At the open section wrong→right 10, right→wrong 5; at the release's
  locks wrong→right 10, right→wrong 10; the successor's own decisions held 6 solved terms; 0 whole
  sections of 8 before and after. The persistence reads at the opening: 64 locks, 6 solved at their
  refinement, each with a later lock; re-read after the later locks, 1 stayed solved and 5 did not.
  This is one development reading, not an acceptance. Both timing moves ran alone on the default
  pool of the host's 24 threads, each under the outer guard `timeout 1800`.

### 4.2 The constrained feasibility witness (the pin §13.3, §14) [measured]

- **Run as pinned**, once: `hnn_prediction -- executed witness order2 2026093061 8 16 7907328
  <out>` at `55f8e62c` (the pin's addendum committed before the run), under the outer guard
  `timeout 8401.536s`; one process on the default pool of the host's 24 threads, no other worker
  running (a game beside it). Development seed `2_026_093_061`, 8 requests, 64 decision terms.
- **Result: no witness found within this procedure and budget.** It stopped when the moves were
  spent: 16 moves, every one adopted under every guard (9 at the ladder's first trial, 7 at its
  second after a `NotBelow` refusal), and the last successor read once more. The strict solved test
  `1 + Σ_(x≠t) U_x < L_t` held at this many of the 64 decision terms, constitution by constitution
  (0 the founded opening, 16 after the last move):

  | Constitution | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | solved of 64 | 0 | 7 | 1 | 2 | 4 | 0 | 4 | 5 | 3 | 1 | 3 | 3 | 5 | 6 | 6 | 3 | 7 |
  | stations right of 64 | 15 | 16 | 15 | 13 | 16 | 20 | 18 | 17 | 16 | 22 | 16 | 18 | 21 | 17 | 19 | 24 | 18 |
  | held decision terms | 56 | 54 | 53 | 55 | 53 | 48 | 53 | 53 | 56 | 49 | 54 | 48 | 49 | 52 | 49 | 45 | 52 |

  No section was whole at any constitution (0 of 8 each; every release released, but the opening's
  7). The own release's `L` fell from `[500197/4096, 500203/4096)` nats at the opening to
  `[342226/4096, 342231/4096)` at constitution 14 and read `[371732/4096, 371736/4096)` at 16; the
  excess `X` from `[318493/4096, 318499/4096)` to `[165990/4096, 165994/4096)` at 14, and
  `[200615/4096, 200619/4096)` at 16. The modulus stayed within
  `[809211/1048576, 829845/1048576]` (from `ρ₀ = 1645392/2097152`); `E`'s largest entry rose from
  `1/2` to `2584579/2097152`, under the entry bound `8`. The ladder started at the excess's
  first-order zero at every move but the last (`EntryScale` at `32`), the start rising from `1/2` as
  the unit move's largest entry fell.
- **The best, and how it was reached**: 7 of 64 at constitution 1 (the earliest of the two sevens),
  one adopted move from the founded opening at `η = 1/2`. At it every request's release locks class
  `3` at every station, one lock a refinement from station 7 down to station 0, and its seven solved
  terms are exactly stations whose target is `3`, read at refinement 0 or 1 (`ℓ` from
  `[12836/65536, 12837/65536)` to `[38913/65536, 38915/65536)` nats). That is a class preference,
  not the key: order-2's targets take the four symbols alike. The best constitution is written as
  its complete continuing state (`witness_best.state`) and printed whole, every decision term with
  its enclosures, in the receipt.
- **The persistence reads** (§13.7), per move at its incumbent, `(solved at their refinement,
  re-read after a later lock, stayed, fell)`: move 0 `(2, 2, 1, 1)`; move 1 `(16, 13, 13, 0)`;
  move 2 `(7, 7, 4, 3)`; from move 3 on no re-read decision stayed solved: `(6, 6, 0, 6)`,
  `(1, 1, 0, 1)`, `(1, 1, 0, 1)`, `(2, 2, 0, 2)`, `(3, 3, 0, 3)`, `(5, 5, 0, 5)`, `(2, 2, 0, 2)`,
  `(6, 6, 0, 6)`, `(3, 3, 0, 3)`, `(6, 6, 0, 6)`, `(4, 4, 0, 4)`, `(5, 5, 0, 5)`, `(3, 3, 0, 3)`.
- **Time and memory**: 2,766,624 ms measured (46 min 6 s by the outer clock), against the
  projection `[1,757,184, 7,907,328]` ms and its two-trial expectation 2,635,776 ms: the measured is
  130,848 ms above the expectation (the ratio `2766624/2635776`) and below the upper end (the ratio
  `2766624/7907328`). Every move ran within the per-move upper bound 494,208 ms (from 109,917 to
  211,948 ms). 34,614,170 ms of CPU, at 1,256 of 2,400 percent; resident 235,536,384 bytes at the
  peak. The run was launched before the waiting standard (`570493d4`) reached this worktree; its
  progress was then watched by one Monitor on its per-constitution line, and its artifacts were
  moved into the worktree's `.local/` from the session's scratch.

The receipts (`2026-09-30_STEP_1B_GATE_A_receipts/`): `timing_move_first_incomplete.txt`,
`profile_two_requests_before_repair.txt`, `profile_two_requests_after_repair.txt` (each with the
temporary phase lines), `timing_move.txt` (the development move's D1, D2 and I7 whole),
`witness.txt` (the witness's every constitution, every move and the best's every decision term) and
`witness_best.state` (the best constitution's complete continuing state); output paths are
replaced by `<out>`.

## 5. The replay [measured]

`bash research/notebook/hnn_design/replay_baseline.sh` at the build (`c48c864f`): "the listing
matches the baseline reference (41 lines)", the read 100,595 ms (its guard 600,000 ms, against the
baseline's recorded 93 s), resident 85,422,080 bytes at its peak; and at the final state (the
harness's label corrections on `d8cc9298`): the listing matches (41 lines), 93,095 ms, resident
84,652,032 bytes at its peak. Evaluation does not use the move, so the guard repairs and the fixed
mask leave the listing unchanged, as required. The two remounts the replay reads (the modulus
record's `E_trained_order2.txt` and `refit_on_lattice.txt`) are labelled partial on stderr
("remount …: partial (E and rho alone; the normal law's Gram, chart, remainders and clock are the
prior's)"); stdout, which the replay diffs, is untouched.

## 6. The gates [measured]

| Gate | Result |
|---|---|
| `cargo check --workspace --all-targets` | clean, no warning |
| `cargo test -p holonics --lib` | 882 passed, 0 failed (871 at `21c98f85`; the eleven of `hnn::tests::lock_face` added), at `c48c864f` (166,080 ms) and again at `d8cc9298` (135,540 ms), on the host with a game running beside it |
| Lean (`tools/lean_check.sh`) | not run: no Lean changed (the owed statements are §7's) |
| the GPU suite | not run: no card-mirrored code changed (`NormalLaw::deposited` and its kin untouched; `ContinuingState` reads the normal law's fields and adds no arithmetic) |

## 7. Owed to #62, stated exactly

No Lean changed in gate A. The build adds laws whose Lean statements are owed; each is held by the
owner's tests named here until it is stated.

1. **The excess's piecewise directional derivative** (`hnn::executed::FirstOrderReading::excess`,
   `ladder_start`; the pin §13.5). For terms `T_j : ℝ → ℝ`, each with an upper Dini bound `b_j` at
   `0` in the form of `lockFace_first_order` (for every `ε > 0`, eventually for small `η > 0`,
   `T_j(η) < T_j(0) + η(b_j + ε)`), and a level `c`: `X(η) = Σ_j (T_j(η) − c)_+` satisfies the same
   form with the bound `Σ_(T_j(0) > c) b_j + Σ_(T_j(0) = c) max(b_j, 0)` (terms below the level
   contribute `0`). It composes `sup_upper_dini` (the two-branch max `max(T_j − c, 0)`) with
   `sum_upper_dini_descends`; the joined statement (`excess_upper_dini`) is owed. Its use is the
   ladder's start only, never a guard: the start `X⁻/(−s_X⁺)` is a first-order prediction across a
   chord (the scope of item (b) below and 1a's item 5). Held by
   `the_ladder_starts_from_the_excess_and_never_divides_by_zero` and
   `the_slope_is_read_on_the_joint_direction`.
2. **The joint direction's first order** (§13.4): the storage move of the joint unit direction is
   `(z(E + D, ρ) − z(E, ρ)) + (∂z/∂ρ)(E, ρ) Δρ`, the derivative of `η ↦ z(E + ηD, ρ + ηΔρ)` at `0`
   (the storage is linear in `E` at fixed weights and smooth in `ρ`), so the certificate on it is
   the joint slope. Owed: the line's derivative (`HNN/ExecutedComparison`, beside
   `modulus_least_squares`). Held by `the_slope_is_read_on_the_joint_direction`.
3. **The restore law** (`ContinuingState`; §13.6). The executed move's successor and receipt are a
   function of the constitution through its continuing state alone: for every opening `Θ₀` and every
   `Θ` reached from it by executed moves, `continued(Θ₀, S(Θ)) = Θ`, hence
   `executed_move(continued(Θ₀, S(Θ)), b) = executed_move(Θ, b)` for every batch `b`, and over any
   finite sequence of batches. Owed in Lean as the retention law's instance
   (`Foundation/Standing`: the continuing state is a quotient of the constitution sufficient for the
   executed move's admitted future), with the move's determinism as its hypothesis. Held by
   `a_restored_checkpoint_continues_exactly_over_successive_receptions`.
   [Noted October 3.] A restore does not recompute the solved chart's residual: `continued`
   (`constitution.rs:7257-7299`) checks shape, opening, material and lattice and loads the chart
   with its saved certificate. Acceptance is protected where a chart is adopted: a deposit's chart
   is published only when its exact integer residual `δ` is at most its target
   (`SolvedChart::deposited`, `constitution.rs:1724-1729`; every other path refuses). From #273 a
   restored state's bytes are bound by its material identity and whole-text check, so a saved
   certificate is the one its deposit certified, read back unchanged.
4. **The decisions' coverage** (§13.4, §13.7): for any lock trajectory whose refinements' placed
   sections grow by the locks, `r*` exists (refinement `0` places nothing) and every station `j` is
   open at `d(j)`, so a request has exactly `m` decision terms on a release, a hold and a refused
   certificate. Owed beside `decisions_release_the_section` (`decisions_cover_every_station`). Held
   by `the_decisions_read_each_station_once_along_the_consistent_prefix` and
   `a_hold_keeps_every_station_obligation`.
5. **The fixed mask's account** (§13.1): the certified decrease is of the mask's composition,
   `C_mask(Θ′)⁺ < C(Θ)⁻` with `C_mask(Θ) = C(Θ)`; it says nothing of the own release's
   `C_own(Θ′)` across a change of trajectory (the context change is a receipt). This is
   `disjoint_enclosures_decrease` on the mask's terms; nothing new is owed beyond the scope note.
6. **Still owed from the pin §3 and §13.7**, unchanged: (a) the release's own lock rule abstracted
   in `decisions_release_the_section`; (b) the certificate reads the chord of the carried move while
   `lockFace_first_order` reads a differentiable line; (c) `θ`'s enclosure from the growths'
   enclosures (now held by `the_lock_face_reads_the_lock_whole_against_its_resting_sheet`);
   eligibility, finite progress, whole coverage and termination of the release (§13.7), measured
   by the persistence reads.

## 8. What gate A decides

Gate A's tests pass, the replay matches and the gates are clean; its witness was not found. By the
pin (§13.3, §14.2) 1b stops at gate A: gates B and C do not open, and the final confirmation seeds
stay unread. "No witness found within this procedure and budget" is not mathematical
infeasibility. The failure is the next loop's subject, named by its measurement: **the candidate's
own certified move, 16 moves on one epoch's 8 order-2 requests, certified a decrease of the fixed
mask's lock face at every move, yet solved at most 7 of the 64 decision terms (each a station whose
target is the class the release then places everywhere), released no whole section, read 45 to 56
of the 64 decisions held at a refinement that did not lock them, and from move 3 on no decision
solved at its refinement stayed solved after the later locks of its section.**
