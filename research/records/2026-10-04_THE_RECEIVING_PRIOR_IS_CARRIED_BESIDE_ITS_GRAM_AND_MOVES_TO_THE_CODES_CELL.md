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
- **Map:** `W′ = x W`. This is the map the law located: `L(φ)` is the code along `φ W`. Doubling
  is exact on the lattice. Halving moves each entry through `map_carry` by its budgeted deposit
  `(x − 1)W` (`Carry::deposit`, Lean `carry_accounting`), so a remainder is carried, not dropped.
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
   - `W′ = x W` holds up to `map_carry`'s accounting;
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
