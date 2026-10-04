# The receiving prior is carried beside its Gram and moves to the code's cell

[agent-inferred; design, October 4] The Rust design for #62's item 4 (comment 5973559786; the
owners named in comment 5975053063): the per-field receiving prior's native form. The mathematics
is `lean/Holonics/HNN/PriorCarry.lean` (#307). The law is record
[2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE.md)
§4. Its selection on the powers of two is §6, which since #307 states the code's cell.

No Rust is edited here. The main line is changing `word.rs` and `ContinuingState` for the default
carry, so this design is read against `948b2599` and re-read against the main line's result before
the code is written. Refs #62, #73, #63.

Objects touched: the receiving map's constitution (its normal law: map, Gram, chart and
remainders), the deposition that changes it, and the ratio whose logarithm is the prequential code.
Of the winding guide's six objects it touches faces and placement (the receiving face's masses and
the map's read of a reading) and the tower thread (the prior's member on the dyadic grid, a scale
restriction). The helix, the pair contact, cell holonomy and the tube are not touched. The
computational object is the receiving read of a helical pair interaction's reading `z_t`, through
the map in force.

Lessons checked ([the failures that repeated](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)):
- **Bits read as progress.** The move decides from the model's exact comparison of two members.
  It reads no code scalar as a score, and nothing is accepted by a code number.
- **A refusal answered with a larger limit.** A comparison inside `ln 2`'s enclosure holds `k`. A
  move whose chart does not certify holds `k`. Neither widens a grid or retries.
- **An authored routine standing in for learning.** The prior is located by the readings'
  covectors through the law. Nothing is tuned toward a task.
- **A design thought in arrays.** Every quantity below is a sum of pairings and variances on the
  receiving face, and the move is a scale restriction.

## 1. What the Rust has, at `948b2599`

- `receiving_fisher_face(samples, unit)` (`constitution.rs:6267`) sums, over one window's samples,
  the alignment `w⟨g, D f⟩` and the curvature `|w|((119/80) Var_p̃((D f)_Re) + ¼|(D f)_Im|²)`.
  Here `D` is the window's own unit step. It returns them for that window's certified step and
  keeps nothing.
- `NormalLaw` holds `map`, `gram`, `chart`, `map_carry` and `gram_carry` (`constitution.rs:1868`).
  The receiving map's law is `RingMaterial::receiving`.
- `ReceiverDeclaration::receiving_scale = k` (`field.rs:256`) founds the prior `2^k I` once:
  `NormalLaw::with_scaled_prior` and `SolvedChart::founded(k)`, whose `scale` is `k`. Nothing
  moves it.
- `Constitution::continuing_state` (`constitution.rs:7206`) saves the source port's law only. It
  refuses where any locus other than `SourcePort(g)` has a clock, so a run whose receiving map
  deposited has no continuing state today.

## 2. The carried pair

**Grain.** Every read of one word's return was read through the same receiving map `W`, the map
before that word's deposit. That map is `law.map()` at `Constitution::prepare_at`, before pass 2
applies the step. So the prequential read at the deposit's grain is `δ_t = W z_t`, with `z_t` the
sample's `feature`. No reading in a window meets its own window's deposit.

**Terms.** These use the same samples (`LinearStep::samples`, not the metric samples), the same
covector `g_t = q − p̃` and the same masses `p̃` that `receiving_fisher_face` derives:

```text
α_t = w_t ⟨g_t,Re , (W z_t)_Re⟩            the code's alignment
σ_t = |w_t| Var_p̃_t((W z_t)_Re)            the code's curvature, in units of ln 2
```

[agent-inferred] The pair takes the real (class) part only. The law it serves, `L(φ)`, is the
code in bits. Its gradient in the class exponents is the real covector, and its Hessian is
`ln 2 (diag p − p pᵀ)`. The phase pairing belongs to the phase comparison, which has its own
curvature bound. The masses are the odometer chart's `p̃`, as the certificate reads them. That is
a declared read: the record's model writes `p`, and `Var_p ≤ (17/16) Var_p̃` on the grain.

**Exact representation.** The at-map pair is `a = A₀ + A₁ ln 2` and `V = S ln 2`, with `A₀`,
`A₁` and `S` exact rationals. A new reading adds `α_t` to `A₀` and `σ_t` to `S`. Only a move
changes `A₁` (§3). Since `ln 2` is irrational the representation is unique, and nothing is
rounded.

**Owner.** Add `LocatedPrior { a0: Rat, a1: Rat, s: Rat }` and carry it as
`NormalLaw::located: Option<LocatedPrior>`. It is `Some` only for a receiving law whose field
declares its prior located (§5). Source and contrast laws carry `None`.
- **Pass 1** (`prepare_at`, `LinearLocus::Receiving`) computes `Σα_t` and `Σσ_t` from
  `law.map()` and `step.samples`.
- **Pass 2** adds them to the stepped law's `located` after `*law = next`.
- One function, `prequential_terms(samples, map) -> Option<(Rat, Rat)>`, sits beside
  `receiving_fisher_face`. It returns `None` where `receiving_fisher_face` does (a covector that is
  not a face's `q − p̃`). It shares the mass derivation, factored out of both.
- The Lean is the fold of `HNN/PriorCarry.carried`. Its `carried_append` is `List.foldl_append`
  and holds for any per-reading term, so the pair after two words is read from the pair after the
  first, and there is no tape. `carried` itself carries the certificate's curvature
  `2|w|((119/80) Var_p̃ + ¼|Δ_Im|²)`, not `σ_t`; the at-map pair's own `carried_eq_sum` (the
  terms above, `moveIm = 0`) lands with the code or goes to #62.

## 3. The move of `k`

After pass 2 commits the receiving law and adds the window's terms, the law reads its pair. The
map's scale is `φ`, with the current member at `φ = 1`. Its members are `x = 2^j`, and member `x`
is the prior `2^(k−j)`.

1. `S = 0`: hold. No curvature locates nothing.
2. `V + a ≤ 0`, that is `A₀ + (S + A₁) ln 2 ≤ 0`: the model's code falls toward the zero map at
   every member. [agent-inferred] Move by one member, `j = −1` (`k ↦ k + 1`). The quadratic
   locates no finite member here, and one member is the least move the evidence asks. The next
   deposit re-reads. Lean owed: `q(y/2) < q(y)` for every `y > 0` when `V + a ≤ 0`, from
   `model_sub`.
3. Otherwise, move to the `j` with `3x/4 ≤ 1 + a/V ≤ 3x/2`, the code-least member
   (`grid_member_best_zpow`). Its two edges are signs of `r + t ln 2`:
   - `2(V + a) ≤ 3xV` is `2A₀ + (2S + 2A₁ − 3xS) ln 2 ≤ 0`;
   - `3xV ≤ 4(V + a)` is `(3xS − 4S − 4A₁) ln 2 − 4A₀ ≤ 0`.
   Each sign is read through `executed::ln_two()`. A sign that is undecided inside the enclosure
   holds `k` and is reported, the way `refining_grain_exponent` does. It is never rounded. A tie
   needs `r = t = 0`, which the enclosure decides.
4. **The floor.** `k′ = k − j < 0` moves to `k′ = 0`. The lattice rule's positivity margin needs
   `k ≥ 0` (record §6). On the members the code descends up to the cell, so `2^0` codes least
   among the admitted members. Lean owed: `2y ≤ x` with `x` the cell member gives
   `q(2y) ≤ q(y)`, from `model_sub`.

The move by `x = 2^j` (prior `s ↦ s/x`) is one atomic successor of the receiving law. If any part
refuses, the unmoved law stands, the deposit stands, and the refusal is reported.
- **Map:** the map's value moves to `W′ + r′ = x (W + r)`, with `r` the remainder `map_carry`
  holds. This is the map the law located: `L(φ)` is the code along `φ W`. Each entry moves through
  `map_carry` by its budgeted deposit `(x − 1)(W + r)` (`Carry::deposit`, Lean
  `carry_accounting`), so the remainder is scaled with the value and carried, not dropped.
  Depositing `(x − 1)W` alone would leave `r` unscaled, and the value would not be `x` times
  itself.
  [agent-inferred] Re-solving `W′ = (W H) X̂′` instead would move the map by a different law, the
  normal equations' minimizer, which the prox iterate `W` is not.
- **Gram:** `H′ = H + (2^(k′) − 2^k) I` on every diagonal entry. The readings' statistic `G` is
  unchanged. `GramBlock::of(H′, 2^(k′))` then finds the same support.
- **Chart:** `SolvedChart` at `scale = k′`, with the off-support value `2^(−k′)`.
  - The support block is warm-started at `x X̂_block` (exact, at exponent `+1` when `x = 1/2`) and
    refined and certified against `H′` by the existing refinement.
  - The new `SolvedChart::moved(&self, gram, k′, rule)` shares the refinement loop of
    `SolvedChart::deposited`. A warm start at `X̂` itself would leave the residual `1 − x⁻¹` on
    the support, outside the contraction for `x = 1/2`.
  - Refused when `δ_ℓ` is not reached.
  - The certificate `‖1 − X̂′H′‖∞` is what `HNN/ChartResidual.inverse_chart_deviation_left`
    reads.
- **Pair:** `rebaseAt x`, in the exact representation:
  `(A₀, A₁, S) ↦ (x A₀, x (A₁ − (x − 1) S), x² S)`.
  - `model_rebase` makes the moved member read the same quadratic.
  - `newton_rebaseAt` and `rebase_into_cell` place the rebased Newton point in the unit's cell, so
    the law does not move again until new readings move it.
- **Reading:** a `PriorMove { from: k, to: k′, held: Option<reason> }` beside the window's
  `ChartReading`. Its `held` reasons are an undecided sign, the floor, a refused chart, or zero
  curvature.

## 4. What `ContinuingState` must save

Today a receiving deposit makes `continuing_state` refuse (§1). The main line's default carry
(read at `9b5d5375` on `claude/main-line-cloud-iia3qw`) adds only the carried end's mount,
`Reference::mount_continued` over `Constitution::continued`, and does not touch
`constitution.rs`. So this change owns admitting the receiving map: `continuing_state` admits each
receiving locus that deposited, and `continued` restores it. A restore stays exact only if the
state carries everything the next deposit and the next move read:
1. **Each receiving `NormalLaw` whole**: `map`, `gram` (with its moved diagonal), and `chart`
   (`exponent`, `scale = k′`, `support`, `block`, `certificate`), plus `map_carry` and
   `gram_carry`. These are the fields the source port's text already writes. `continued` checks
   each map's shape against the declared receiving port, as it does the source port's.
   - The text's chart line must gain `scale`. It writes `chart exponent certificate`, which is
     enough only while every saved law is at `k = 0`.
2. **The pair**: `A₀`, `A₁` and `S`, exact, on a line `located a0 a1 s`, or `located none` for a
   held law.
3. **The receiving locus's deposit clock**, which the budgeted carry's precision reads, as the
   source port's clock is saved.
4. **`material_identity`**: each receiving law is set to its founding before the residue, where
   the source law is set absent. That founding is `with_scaled_prior(0, declared k)` with `located`
   at its founding: zero where the field declares `Located`, `None` where it declares `Held`. Then
   a moved `k` or a grown pair does not change the identity. The declaration (§5) stays in it, so a
   located state mounted on a held opening, or the reverse, is refused.
5. **The lattice check**: `on_lattice` already reads the Gram's entries, so it covers the moved
   diagonal `2^(k′)`. `from_text` must refuse a `scale` whose off-support value is not
   `2^(−scale)`.

The check line and residue are unchanged. Every new line sits before `storage-product`, inside the
check, because `ContinuingState::stamped` replaces only what follows `storage-product`. Adding
`located` to `NormalLaw` changes the constitution's written form, so every identity changes and
earlier saves are refused, as the layout law in `material_identity` states. `from_text` has no
default for the chart's `scale` or for `located`, so a text written before this layout is refused
even after `stamped` re-stamps it. Old saves are superseded prototypes.

## 5. The declaration

`ReceiverDeclaration::receiving_scale: u32` becomes `receiving_prior: ReceivingPrior`, with
`ReceivingPrior::Held(k)` and `ReceivingPrior::Located { from: k }`.
- Every field declared today becomes `Held(k)` at its current `k`: campaign 1 keeps `Held(1)`
  (`field.rs:371`), and the rest `Held(0)`. Their behaviour is byte-identical.
- [agent-inferred] The moving law is opt-in, like the carry was (#285), because it changes the
  HNN's behaviour. A field moves to `Located` in its own change. That change's merge gates are
  CLAUDE.md's: `cargo check`, the changed laws' tests, and the GPU suite, since it changes the
  HNN's behaviour. The main line's read of it on campaign 1 is its receipt, as `2 I`'s read was
  (#259), not a gate.
- [Superseded, October 4, by §8] No receiver holds its prior: the declaration names only the
  founding member, `receiving_prior: u32`, and every receiving law carries its pair.

## 6. The tests that change, and the new ones

These change mechanically, with behaviour unchanged:
- **Every `ReceiverDeclaration` literal** (`receiving_scale: k` becomes
  `receiving_prior: Held(k)`):
  - `tests/encoding.rs:175`, `tests/prediction.rs:236`, `tests/propagation.rs:783`,
    `tests/support.rs:160` and `tests/keys.rs:47`;
  - `tests/receiving.rs:58` and `:91`, and `tests/learning.rs:54` and `:117`;
  - `tests/retention.rs:359`, `:479` and `:554`;
  - `holonics-cuda` `hnn/tests.rs:178` and `hnn/port_tests.rs:97`;
  - `field.rs:371`.
- **`tests/constitution.rs:603`** `a_scaled_prior_carries_its_chart_off_the_support`. Its
  `NormalLaw` equalities hold with `located: None` on both sides.
- **`tests/lock_face.rs:696`, `:791` and `:839`** (restore over successive receptions, refusal on
  foreign or damaged text, the reception's end inside the check). They read the new text lines.
  Their identities are computed in the test, so they hold.
- **`holonics-cuda` `hnn/physics_tests.rs:102`** (the scaled prior's card parity) is unchanged.

New tests, at host gate 2. The last runs on the card at gate 3.
1. **The terms are read before the deposit.** On a two-word receiving run, `located` after the
   first word equals `prequential_terms(word-1 samples, W₀ = 0) = (0, 0)`. After the second it
   equals `prequential_terms(word-2 samples, W₁)`, computed independently.
2. **No tape.** The pair after `n` words is the sum of the per-word terms, the Rust face of
   `carried_eq_sum`.
3. **The move.** A field whose pair puts the Newton point in a neighbour's cell checks five things:
   - `k` moves to that neighbour;
   - the Gram's diagonal moves by exactly `2^(k′) − 2^k`;
   - `W′ + r′ = x (W + r)` holds exactly, on a fixture whose remainder is nonzero;
   - the chart certifies at `scale = k′`;
   - the pair is rebased by `rebaseAt` exactly, and an immediate re-read holds.
4. **Held is unchanged.** A `Held(k)` run's receipts are byte-identical to today's.
5. **The enclosure holds `k`.** A pair whose edge sign lies inside `ln_two()`'s enclosure holds
   `k`, and the reading reports it.
6. **The floor.** A cell below `k = 0` moves to `0`.
7. **Restore across a move.** Once `ContinuingState` carries the receiving map, a state written
   after a move restores, and the next word equals the uninterrupted one exactly.
8. **Card parity across a move** (gate 3). The card's deposit reads the moved dense Gram and chart.

At the code's landing, the atlas row `hnn.receiving-prior-carry` gains its `R:` owners. The row
`hnn.receiving-prior-scaled-chart` changes `k declared` to `k founded by the declaration, moved
where located`. The two owed Lean lemmas (§3, steps 2 and 4) land with it, or go to #62.

## 7. What landed with the code

The Rust follows §§2–6, with these additions, each decided from the law:
- **Two more held reasons.** `PriorHeld::Carrier` holds `k` where `k′` would pass the carrier's
  residual shift (`RESIDUAL_SHIFT`), since `2^(k′)` and `2^(−k′)` must stay on the carriers the
  chart and its remainders use. `PriorHeld::Unread` holds `k` where a stepped receiving map's
  samples are not a face's `q − p̃` (`prequential_terms` returns `None`), so no term is added and
  nothing is guessed.
- **The certificate.** `PriorMove` carries the moved chart's certificate `‖1 − X̂′H′‖∞`, so the
  reading states the bound `HNN/ChartResidual` reads.
- **Where the pair is read.** It is read only at a deposit whose covector reached the receiving map
  (a linear step at `LinearLocus::Receiving`). A deposit that stepped only the source port, or
  nothing, adds no term: its readings never reached the map. On the chain at its capacity located
  from `2^6`, the reference port's exposure published 35 deposits and read the pair at 33 of them.
  It moved six times: `6 → 0`, held at the floor, with certificate `65275/2^28`
  (`65275 = 5²·7·373`), then one member per move, `0 → 1 → 2 → 3 → 4 → 5`, with certificates
  `3967/2^26` (3967 prime), `1/2^16`, `1/2^18`, `1/2^20` and `1/2^22`. The climb is the law below.
- **The climb where no member codes least.** At `V + a ≤ 0` the move exits down (`j = −1`,
  `k′ = k + 1`), and the rebase keeps that branch: `rebaseAt_add` gives `V′ + a′ = x (V + a)`, and
  `exit_down_iterate` gives that `V + a ≤ 0` survives every halving with half the map still coding
  strictly less, and `model_lt_of_add_nonpos` gives that `q` is strictly increasing on `[0, ∞)`
  there (Lean `HNN/PriorMove`, #318). So while the readings keep `V + a ≤ 0`, no member codes least,
  and the prior rises one member per read until new readings lift `V + a` above zero or the carrier
  stops it. That is the law, not a runaway; `j = −1` sets only the pace. `moved_map_accounting`
  there states the map's move as `W′ + r′ + e = x (W + r)`, with `e` the deposit's staged release.
- **The carrier limit.** The port's outcome there is a declared reading:
  `PriorHeld::Carrier`, reported in that deposit's `PriorMove` with `from = to = k`, the deposit
  standing and the law unmoved. `RESIDUAL_SHIFT = 125` is the `i128` carrier's width (the
  representation's `2^(L_s + e_H)` with its sign and one bit of headroom), not a chosen constant.
  The first build checked it only on the cell branch, so the `V + a ≤ 0` branch would have moved
  past it; `member` now holds there too. The host test
  `where_no_member_codes_least_the_prior_rises_until_the_carrier_holds_it` reads `j = −1` through
  the halvings from `k = 5`, `j = −1` at `RESIDUAL_SHIFT − 1`, the hold at `RESIDUAL_SHIFT`, and a
  law at `k = 125` whose deposit returns it unmoved with the reading `(125, 125, Carrier)`. A chart
  that refuses to certify before that limit is the declared hold `PriorHeld::Chart`.
- **The saved law is verified before it is read.** `ContinuingState::from_text` checks the length
  and residue line before reading any line, and `read_law` refuses a prior past `RESIDUAL_SHIFT`
  before it forms `2^k`, so a damaged save is refused, never allocated.
- **The card.** It deposits through the host's `Constitution::deposited`, so a moved Gram, map,
  chart and pair are the reference's, and the lockstep compares the published constitutions after
  every deposit. The normal-law mirror re-steps a fixed `2^k` on its kernel, so it skips a deposit
  whose prior moved and counts it (`NormalMirror::moved`). The card test is
  `the_card_port_returns_the_reference_across_a_moved_receiving_prior`, at the production
  reception (the carry).
- **At rest a map that never leaves zero locates nothing.** On the card's chain and cut at rest,
  every deposit's move of the receiving map stays below the map's lattice grain at the prior `2^6`
  and is carried as the map's remainder. The map in force reads zero at every window, so the code
  along `φ W` is the same at every member, `S = 0`, and all 33 reads hold `k` for want of curvature.
  No member is distinguishable by those readings, so holding is the law. Under the carry the
  carried motion reaches the map, it leaves zero, and the same cut moves the prior 22 times in 33
  reads (`at_rest_the_cards_chain_holds_its_prior_and_under_the_carry_it_moves`). The card test's
  first run, at rest, read 33 times and moved none, as the law says.

The owed Lean (§2's at-map `carried_eq_sum`, and §3's `q(y/2) < q(y)` at `V + a ≤ 0` and
`q(2y) ≤ q(y)` at `2y ≤ x`) is filed on #62.

## 8. The located prior is the production default

[agent-inferred, October 4] Which receivers, if any, keep a fixed prior? None, by the law, so
`ReceivingPrior` is gone and the declaration names only the founding member `k`
(`ReceiverDeclaration::receiving_prior: u32`). This is derived as #310 derived the carry's default
(the carry record §8, `A = 0`): a held prior would be one more exterior constant at the reception,
and the reception has none to spare.
- **Deposition is the only law that changes a constitution, from the covectors that reached that
  locus** ([objects §8](../../docs/ELEMENTARY_OBJECTS.md#8-deposition)). The prior `2^k I` is part of
  the receiving law's constitution: it is the Gram's founding diagonal. The covectors that reach
  the receiving map are exactly the readings whose terms locate it (§2). Holding `k` while those
  readings arrive keeps a part of the constitution that the reaching covectors cannot move. That is
  an authored constant, not a law.
- **Every lawful reason not to move is already the located law's own reading.** No reading reached
  the map: no term is added. A reading is not a face's `q − p̃`: `Unread`. Zero curvature:
  `NoCurvature`. A sign inside `ln 2`'s enclosure: `Undecided`. The floor, a chart that does not
  certify, the carrier limit: `Floor`, `Chart`, `Carrier`. Each holds `k` and says why, in the
  deposit's `PriorMove`. A declared hold adds no case these do not cover.
- **`k` is the prior's initial configuration, a key's and not a choice held.** The founding map is
  `W₀ = 0`, so the founding pair is zero (§2), and the mount reads no terms and moves nothing. A
  rest-declared receiver therefore mounts without movement, as a rest-saved state mounts with zero
  carry. `the_founding_carries_a_zero_pair_and_the_mount_moves_nothing` reads it at `k = 0, 1, 6`:
  the founding Gram is `2^k I`, its chart exact, its pair zero, and its first window holds with
  `NoCurvature`. The at-rest bullet of §7 is the same law over a whole exposure.
- **Campaign 1 founds at `2 I`** (`receiving_prior: 1`, the member its readings located on 3,400
  readings: the October 2 record), and every other field at `I`. Both move from there.
- **A continuing state keeps the founding.** The founding member stays in `material_identity`
  (§4.4), and `continued` refuses a receiving law founded at another member. So a state saved from
  one founding is not mounted on another.

**The tests this changes, and why.**
- Every `ReceiverDeclaration` literal names `k` instead of `Held(k)` or `Located { from: k }`. The
  prior-carry tests read the founding as above (`chain_at(from)`), and the restore test opens
  another founding at `k = 5` to read the refusal.
- **The budgeted carry's ledger** (`tests/constitution.rs`:
  `the_budgeted_carry_accounts_for_every_update`,
  `the_release_since_the_founding_stays_below_half_a_unit`,
  `the_carried_gram_stays_positive_definite`). The chain's receiving prior now moves on that run.
  Its Gram's first diagonal entry ended at `4 + 105/2^24`, where the step-only ledger expected
  `1 + 105/2^24`: the moves shifted it by `2² − 2⁰ = 3`. A move is one more update of the carried
  arrays: `(2^(k′) − 2^k) I` on the Gram, `(x − 1)(W_s + r_s)` on the map. Its step is taken at the
  stepped successor's chart, which the move then replaces. The ledger now reads both. It reads the
  step at its own chart from the same deposit on the predecessor without its prior pairs
  (`Constitution::without_prior_pairs`, test-only), then adds the move. Every identity is
  unchanged: value plus remainder plus releases equals the exact sum of the updates. The exact Gram
  is the prior in force plus the statistics, and that is still `⪰ I`. The run's move is asserted,
  so the ledger reads one.

**The card tests it moves.** The lockstep's host side, read in the cloud, gives the prior reads and
moves on each card fixture at the production reception (at rest in brackets). Every count those
tests assert is unchanged.
- `the_card_port_returns_the_reference_on_the_chain`: 33 reads, 31 moved (rest: 23).
- `the_card_port_returns_the_reference_on_a_generic_constitution`: seed 5, 11 reads, 2 moved
  (rest: 0); seed 11, 11 reads, 11 moved (rest: 11).
- `the_card_port_returns_the_reference_on_campaign_one`: 7 reads, 1 moved (rest: 6).
- `the_card_port_returns_the_reference_with_resonators`: 7 reads, 4 moved (rest: 2).
- `the_loaded_source_matches_with_y4_and_hop_two`: no read. Its 7 refused deposits and stepped
  nothing.
- `the_card_port_returns_the_reference_on_the_standing_cut`: private, read by the card run.
- Every other card test whose deposits step the receiving map reads the prior through the host's
  `Constitution::deposited`, as the card does. The published constitutions are compared after
  every deposit, and the normal-law mirror skips each moved deposit and counts it
  (`NormalMirror::moved`). The GPU suite is the receipt.

The moves under the carry, in order:
- the chain: `0 → 1 → 0 → 1`, then `1 → 2 → … → 29`, one member per read;
- seed 11: `0 → 1 → … → 11`, one member per read;
- seed 5: `0 → 1 → 0`;
- campaign 1: `1 → 0`;
- the resonators: `1 → 0 → 1 → 2 → 4`, the last a cell move of two members.

The runs of one member per read are the climb of §7: those readings keep `V + a ≤ 0`, so no member
codes least. A climb stops when new readings lift `V + a` above zero, or at the carrier hold.


## 9. The U6 states and the receiving map, with the carry and the located prior both the default

[measured-diagnostic; October 4, on `24d1fd3e`; bounded host reads on the cloud host] The standing
finding is that U6 states have a zero receiving map (the refit-ingredients record §7; the record
[The receiving map opens at zero](2026-10-02_THE_RECEIVING_MAP_OPENS_AT_ZERO_AND_THE_SOURCE_MAP_REACHES_THE_CONTACT_ONLY_AS_MOTION.md)
§1). It still holds, and neither default changes it. The link that holds `R` at zero is the
comparison. The saved-state link no longer zeroes `R`: since `aaf2bd43` it refuses every U6 state.

**The comparison holds `R` at `R₀ = 0`, by the deposition law.** Step 1's chain runs
`hnn::executed` over the bank's release and `ReceivingBank`, and its move is
`Constitution::stepped_source`, which writes `rings[ring].source` and the source port's clock and
nothing else. The bank reads the receiving ring's storage through its members' turn
`ρ(M_m(z))`; `R` is not on that forward path, so no covector of the chain reaches it, and
deposition changes only a locus a covector reached. The carry and the located prior are laws of
the reference port's reception and of a deposit at `LinearLocus::Receiving`. The chain runs
neither: it never runs `Word`, the reception or a receiving deposit (THE_REBUILD, the
consolidation inventory). Even a prior move would leave `R` at zero: the move deposits
`(x − 1)(W + r)`, and `W + r = 0` there, so `x(W + r) = 0`.

**The saved state no longer mounts.** Before `aaf2bd43`, `continuing_state` refused any clock
other than the source port's, so a U6 state certified every other locus unmoved, and `continued`
left `R` at the opening's founding: zero by construction. Since `aaf2bd43` the state's text
carries `chart exponent certificate scale`, a `located` line and a `receiving` section. All 21
files under `research/runs/u6/states/` are listed in the manifest of earlier states and carry
none of these, so the stamp passes them and `ContinuingState::from_text` refuses them. Read with
the notebook's own mount, `m6` and `w16` are refused with "the continuing state refused: the
chart's scale". No U6 state can be read at `24d1fd3e`, nor on main since #319.

An exact conversion exists, because the earlier writer certified what it left out:
- the source law's chart at scale `0`, with `located none` (`from_text` requires both of the
  source law);
- `receiving 1` with the declared receiver's law at its founding, clock `0`.

Whether the states are rewritten once in the current layout or retired belongs to the U6
consolidation. Extending the stamp into a layout decoder would be a legacy decoder.

**Where `R` first moves: the receiver's own comparison, from the U6 opening.** The exposure
protocol (`Reference::campaign_one()`, the carry, founded at `k = 0`) was mounted on the U6
opening (`founded_opening`, where every U6 state's `R` stands) and read deposit by deposit:
- **Window 1.** Nothing steps. No source has entered yet, so no reading reaches `R`.
- **Window 2.** `R` alone steps, at `2^(−2)`, and 872 of its `10·120 = 2^4·3·5^2` entries become
  nonzero. The prior is read once and held as `NoCurvature`: the pair reads `δ = W z` at the map
  before the deposit, which is zero, so both terms are zero.
- **Window 3.** This is the first reading of `R₁`. Fifteen loci step: both elements, both
  channels, the source port and the standing, beside `R`. This is §5 of the opening-at-zero
  record: every covector into the passage is `Rᵀg`. The pair now has terms and the prior moves
  `0 → 1`.
- **Windows 4 and 5.** The prior moves `1 → 2 → 3`, one member per read. After each move
  `V + a < 0` (`ln 2 < 7/10` bounds it), so this is §7's climb: no member codes least.

So the first nonzero `R` is window 2's deposit, and the first reading that sees it is window 3's
compare. The six-window exposure's curve gives the same: no step at commit 1, `R` alone at
commit 2, and from commit 3 on the elements, channels, source port and standing beside `R`.

**What it changes for step 1's chain.** The chain itself is unchanged: `R` is outside its path,
so the zero map is not step 1's blocker. Step 1's blocker remains the native move's path to a
representation. What `R = 0` bars is a read of a bank-chain state through `R`: `word-read`, and
§6's contact-path read. The carry's repair reaches step 1 only if its chain deposits through the
receiver's own comparison. Then `R` forms at the second window, and the native contact return
deposits on `C`, `E` and the standing from the third. That route is the exposure protocol, the
gate the refit-ingredients record §7 restated. On the existing U6 states this cannot be read
until they mount again.

Receipts (a scratch notebook command, not committed; debug build):
- the one-window read with the two mounts: measured 43,473 ms;
- the six-window exposure: projected at most six windows at the one-window read's 41 s each,
  deadline 400 s, measured 57,023 ms;
- the five-window deposit read: deadline 300 s, measured 50,582 ms.

Peak resident sets were not read.
