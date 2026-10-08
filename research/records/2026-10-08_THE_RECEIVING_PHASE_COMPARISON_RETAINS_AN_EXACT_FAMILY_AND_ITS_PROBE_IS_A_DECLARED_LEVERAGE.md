# The receiving phase comparison retains an exact family, and its probe is a declared leverage

Refs #73, #62, #63. Source in `.local/wt/hnn-ask-loop` (branch `claude/hnn-ask-loop`, from
`11648e5705dc4dbbc0595f3ea5cb61c8b6d2d919`). Nothing here has been compiled, tested or run yet:
the sole native-validation queue owns every compile, and its receipts will be added here. Claude
leads the workflow from this record on; Epime (Codex) reviewed every law below read-only.

The computational object is the helical pair interaction. This work touches the pair (the
receiving map) and faces and placement (the receiving face's masses, phases and grain cells);
helix, cell holonomy, tube and tower thread stay attached unchanged.

## 1. The October 8 request was out of image by construction

The scoped v113 run held before either encounter. The handoff's diagnosis stands: no control in
the declared `Q²` reaches the quiet request. Its cause is visible in the declaration itself. The
request is the zero vector on four realified rows `[Re f₀, Im f₀, Re f₁, Im f₁]` at one station,
and the source port has two controls (`B = E_source: Q² → Q⁸`), so `rank L ≤ 2 < 4`: an exact
carrier is generically outside the image, and the two exact (ungraded) phase rows alone use both
controls. From the saved operands, the least Chebyshev distance of the request to `im L` is

```text
t = 5871876900421564824468641258173283 / 2236157012288493224071150466536934400,   2⁻⁹ < t ≤ 2⁻⁸
```

(exact rational elimination over every three-row alternation of the four rows; no HNN passage).
[agent-inferred] An exact carrier equality on a receiving face is not a lawful goal declaration:
the receiver reads magnitudes at its grain and phases exactly, so a goal declares its magnitude
cell, its phase grain and its quantifier. The v113 request is not changed or rerun; its Hold
remains correct and is kept as a regression.

## 2. The integrated objective and what the first step claims

The loop Brandon asked for is: learning changes perception and selection, and a selected
encounter's actual consequence changes the next learning and selection. Its missing operand was a
retained family of alternatives with a certified observation partition, consumed by
`receiver::release`'s Ask. No HNN caller offered Ask (every `LawfulOptions::assemble` on the HNN
path passed `None`), and the plural sets the executed path computes (the key fibre, the repair's
class fibre, a plural control fibre) collapse to a fallback or a Hold.

The first step (C1) is restricted, after Epime's review, to **certified native distinguishability
within a declared inner family**:

- the family is a set of *hypothesized receiving relations* `V`, read from exact statistics of the
  actual receipts. The machine's actual state (its map, carries, native current and the World's
  current) is known and singular; `V` is never a state alternative;
- it claims no truth inclusion, no probability or information, no nesting or shrink of the family
  after a receipt, no outer completeness and no Act;
- the prospective feature it is read at is the **native** carrier, which does not model the World's
  reflected return (`word/action.rs` certifies a native relation, not a World prediction). A World
  face outside every predicted block is reported as falsification of the native prediction, never
  assumed contained.

## 3. The phase family

[definition; agent-inferred] A receiving map's phase rows read, for class `c` at the realified
native feature `x`, the lifted phase `y_c = v_cᵀx/2`. An actual receipt `k` (weight `w`, feature
`x_k`, observed masses `q_k`, lifted doubled targets `t_kc = 2φ̂_kc`) contributes the exact phase
comparison `(w q_kc/8)(t_kc − v_cᵀx_k)²`. Its gradient is the comparison's phase gradient; the deposited sample carries the negative, the descent covector `+½q_cΔ_c`, and the producer reads `t` back with that sign. The sum
is exactly quadratic, so its sufficient statistic is, per class,

```text
S_c = Σ w q_c x xᵀ,   m_c = Σ w q_c t_c x,   s_c = Σ w q_c t_c²,   N = Σ w·#{c : q_c > 0},
```

absorbed in the deposit's own successor through the map in force before it, and saved and
restored exactly. No sample is kept. Under the receiving law's prior ridge `2^k I` (a declared
convention of the family, not a deposited loss) and the declared cumulative tolerance
`τ = ε_bits·N`,

```text
F_τ = {V : Σ_c (1/8)(v_c − v̂_c)ᵀ A_c (v_c − v̂_c) ≤ τ},   A_c = S_c + 2^k I,   v̂_c = A_c⁻¹ m_c,
E(x) = {y : Σ_c (y_c − ȳ_c)²/(2ℓ_c) ≤ τ},   ȳ_c = v̂_cᵀx/2,   ℓ_c = xᵀ A_c⁻¹ x,
```

by Cauchy–Schwarz in the `A_c` metric. The outcome blocks are the lifted half-open arcs
`[j/L, (j+1)/L)` per class that `E(x)` meets. They are decided exactly on squares, with the infimum
over a half-open box counted only when attained, and two feasible witnesses are given in two
distinct blocks. At the same feature, a receipt contracts the leverage exactly,
`ℓ′_c = ℓ_c/(1 + w q_c ℓ_c)` (Sherman–Morrison), and nothing more is claimed. Owner:
`hnn::phase_family`; atlas `hnn.receiving-phase-family`.

**Why the phase rows and not the class rows.** The class (magnitude) comparison's covector is the
odometer face `q − p̃`, constant on grain cells and the gradient of no scalar. Its misreading of the
smooth gradient is bounded for every target (`HNN/Ratio/Resolution.odometer_mismatch_le`:
`|⟨p − p̃, m⟩| ≤ (K − 1)Σ_c p̃_c|m_c − m_t|`, with `K = 2^(1/L)·2/(e ln 2)`). Turned into a
quadratic family, that slack per reading is of the order of `(K − 1)²`, comparable to the per-cell
`ε = 1/16` at `L = 16`, so a certified class family is empty or vacuous at the receiver's own
tolerance. That is the measured blocker of a class family. The phase comparison `½q̃Δ²` is exact.

## 4. The leverage probe

A continuum family has no class counts, so `receiver::release` gains
`ProbeSeparation::{Counted, Leverage}`. A `LeverageSeparation` is offered only when the probe's
outcome meets at least two exact blocks and its declared leverage strictly exceeds its
comparison's. The leverage is a convention compared exactly, not an entropy or a guaranteed gain.
The counted partition and `release` are unchanged. Atlas `release.leverage-probe`.

## 4b. The Ask consumer on the action path

[definition; agent-inferred] `Word::prospective_feature` reads, at the one compared station, the
native feature the receiving map multiplies, as an exact affine function of the admitted control,
`x(u) = x₀ + J u`. It mirrors the request path's checks, and its consumer equation is checked in
tests: `R x₀` is the request path's baseline, and `R J` is its response, row by row.
`AdmittedWaves` declares the finite probe set: the controls `u ∈ 2^(−j)ℤ^m` whose model
preparation work `P(m + Bu) − P(m)` (the owner's `PowerForm::ring_power`, cross term included and
possibly negative) does not exceed the declared supply. `B` must have full column rank, and a
declared enumeration capacity refuses, never truncates.

`PreparedPhysicalProbe::ask` reads the receiving law's phase family at `τ = ε_bits·N`. It offers
through `receiver::release` the admitted wave whose image meets at least two blocks with the
greatest total leverage; ties fall to the lexicographically least `u`, a declared convention.
Otherwise it holds, with a typed reason. `encounter` executes exactly the request path's actual
World encounter, return, carry publication, comparison and deposit through one shared private
execution. It returns the native prediction made before the encounter, and a `PhaseDiscrepancy`
that reads the actual World face's lifted phase block against it. A miss is falsification of the
native prediction. With no receipt yet (`N = 0`) the family is a single member and the first
decision holds, so the family is founded by earlier receipts, such as the receiver's prior
observations.

Brandon's lens of October 8 (relayed by Epime): noise is an unresolved field of possibilities, and repeated traversal over the terrain organizes it into music, repair or generation. Here the declared family is that unresolved field. Each actual encounter is a re-traversal that updates the comparison's sufficient statistics, and the declared family is then recomputed. This is not a restriction: the centre moves, `τ = ε·N` changes, and neither nesting nor truth coverage is claimed (an actual World face can fall outside the native prediction). Release at tolerance is the organization. The lens adds no subsystem. It keeps physical iteration, prediction and learning publication distinct in their accounting while they share one state.

## 5. Located defects in the receiving deposit

- **Soft faces were misread (repaired).** `face_masses` reconstructed `p̃` from the covector,
  assuming a one-hot target. On the action path the target is a soft World face, and with two
  classes the reconstruction is always accepted and wrong: `p̃ = (½, ½)` against `q = (⅔, ⅓)` is
  read as `(⅚, ⅙)`. It fed the class metric, the Fisher face and the located prior on every World
  receipt. Fix: `Sample.masses` carries the face's exact `p̃` from the same `ReceivingFaceRatio`,
  `face_masses` validates and prefers it, and the one-hot path is unchanged. Atlas
  `hnn.soft-face-masses`.
- **The certified step's alignment omitted the odometer's misreading (repaired).** The certified
  decrease is of the smooth score at the grain representative, whose linear term pairs the smooth
  `p − q` (`HNN/Ratio/Certificate.codeLength_add_le_odometer`). The deposit paired the odometer's
  `q − p̃` and never formed `p − p̃`. The target cancels in that gap. At the representative the
  masses lie within `K = 2/(e ln 2) < 17/16` of each other, so the certified alignment is

  ```text
  a_cert = a − (1/16)·Σ_t |w_t|·min_s Σ_c p̃_tc |Δ_tc − Δ_ts|,
  ```

  and an alignment at or below zero, or a face whose masses are unread, refuses the map's step
  while the Gram and chart move. Step sizes can only shrink, so regressions are re-measured, not
  matched. Atlas `hnn.receiving-certified-alignment`.
- **The Fisher face's `119/80` (checked, unchanged).** It is the constant of the declared object:
  `codeLength_add_le_odometer` is stated on the grain, with `p ≤ (17/16) p̃` and `ln 2 < 7/10`. The
  `8/5` in its doc is the constant for actual off-grain logits, which are not the certified object.

## 6. Consecutive encounters are admitted

The action consumer's guard admits only an at-rest navigator lift. An encounter publishes the
physical carry, never the lift, and the next opening consumes the carry (`reception_opening` →
`open_source_exact_received`, `opened_at = carry.ticks`, and the World's native tick ties to it).
So two encounters on one receiver and one World are admitted today. A nonzero lift while a World
is bound (a World face chart under a lift) is outside this path.

## 7. The World's reflected return: the next law (C1b)

[definition; agent-inferred, Epime's design] The learned World model is a native port Holon: its
constitution and carried storage and contact current, with `ξ⁺ = Fξ + Ga`, `b = Pξ + Qa` and the
face `Cξ⁺ + o` as transient charts of the existing Holon law. It is not a dense kernel or a chosen
memory window, and inference never imports the actual World's coefficients.

- The free response is mandatory.
- For a fixed model the prospective whole-word map stays affine in the prepared wave. Under an
  uncertain model the image is the correlated joint set, never a product of independent bounds.
- The exact filter for a fixed model keeps an affine current fibre `c + N k`. It filters by the
  complete preimage of each actual `(a, b)` and carries every solution forward.
- Across a native-kind key family the filter keeps one fibre per compatible key, which is the
  key-location form of learning.
- The memory's state advances through every actual World step, even when a comparison or
  deposit refuses.

The bounded C2 acceptance (two actual encounters, a prediction cover before the first, and a
state-only matched control at the continuing crossing) waits on that model and its finite
forward certificate. The combined World/material derivative remains a separate obligation, and
v111's zero C/K/D movement stays its failed gate.

## 8. Obligations carried to #62

- the phase family's image (Cauchy–Schwarz), the Sherman–Morrison contraction and the half-open
  block rule;
- the leverage probe's outcome ball and contraction;
- the composition of `codeLength_add_le_odometer` with `odometer_mismatch_le` for a soft target.

## 9. Receipts

**v114 (superseded pin `62bbc7f07`).** The workspace all-targets check, 57/57 doctests and the
library-test build passed. The guard lints failed on five notebook filesystem and process uses
inherited unchanged from base `11648e57`. The queue stopped there, so no runtime or mathematical
acceptance carries forward. Receipt: `receipts/2026-10-06-lean-rust-native-queue/continuation-v114/`.

**v115 (packet 5, `51f7806ddba2399af6c6d02dd27e2f5c54694a22`, all 316 native inputs sealed).**

- Gate 1 passed: the workspace all-targets check, the all-targets guard lints (which close the five
  v114 diagnostics) and 57/57 doctests.
- 143/143 scoped runtime tests passed:
  - 125/125 selected library tests (`receiver::release`, `receiver::population::chaser`,
    `hnn::phase_family`, `hnn::tests::{constitution, prior_carry, guards, retention,
    rebase_boundary}`);
  - 10/10 `physical_ask`;
  - 4/4 `physical_action`;
  - 4/4 `native_action_return`.
- The `holonics-cuda` all-targets check passed. It was compile-only, with no GPU workload.
- Stage times, measured against a 65 s guard per compile stage:

  | Stage | Wall (ns) | CPU (ns) | Group peak (bytes) |
  |---|---|---|---|
  | workspace check | 13 091 000 775 | 23 551 201 000 | 2 003 533 824 |
  | guard lints | 18 003 983 010 | 30 008 251 000 | 2 202 677 248 |
  | doctests | 22 156 454 199 | 40 033 059 000 | 2 772 676 608 |
  | lib-test build | 24 001 880 146 | 36 310 756 000 | 2 777 206 784 |

  The 27 new native and guard units cost CPU `196507593000 ns` and wall `143301555466 ns`.
- No earlier `physical_action` or `native_action_return` assertion changed against `11648e57`, and
  the v113 obstruction still holds.
- Receipt: `receipts/2026-10-06-lean-rust-native-queue/continuation-v115/VALIDATION.json` (sha256
  `050cb6dcfd8acdac49a28a885a5408acaba6e8bb4ddc7271e6d143b117ea3cb6`).

**What v115 does not establish.**

- No World truth coverage, whole-HNN learning or mathematical acceptance.
- The hold/ask/ask integration test executes a zero wave after the first Hold, to found the
  phase statistics. That is admission and continuity mechanics, not an autonomous Ask bootstrap.
- R5's effect on receiving tests outside the selected modules (the text path) was not run in v115.
- The independent consumer review's repairs (`faac32f00`, `19b2dcc10`, `d7e2e5988` and this
  commit) follow v115 and need their own run.
