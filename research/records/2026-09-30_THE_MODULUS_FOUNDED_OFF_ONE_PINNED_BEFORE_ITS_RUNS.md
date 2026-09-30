# The modulus founded off one: the lossless boundary traps the certified move, and the modulus moves by its least-squares step (pinned before its runs)

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
deciding measurement (§1: development seeds 32, 41, 42 and 43 only, an exterior diagnostic, not a
pinned run); [definition; agent-inferred] for the law's choice and the pins; [proved-derived;
formal-checked] for Lean `HNN/IndexedOpen` §6 and `HNN/ExecutedComparison` §6;
[proved-derived; implemented-exact] for the owners' laws held by their tests.

**Occasion.** The [station-framed placement's result](2026-09-30_THE_STATION_FRAMED_PLACEMENT_MEASURED_THE_REFIT_READS_BOTH_CHAINS_AND_THE_CERTIFIED_MOVE_KEEPS_THE_MODULUS_AT_ONE.md)
§7 fixed this loop: the refit under the station-framed law reads order-2 (96 whole sections of 128
at `ρ = 137573/262144`), and the native certified training kept the modulus at one in all 16 moves,
releasing 0 whole sections on its confirmation; the modulus's slope `γ_ρ` was negative on every
development move read. The experiment named there: `γ_ρ` split by term kind. It is read here
(§1); the law it forces is derived (§2), built in its owners (`6dc1e5ae`, §3) and pinned (§4)
before any measured run.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches three: **the
tube** (the span's transport and its decay: the modulus and its founding), **faces and placement**
(each datum's weight read from its station, the one-turn alias on the weights' chart), **the cell
holonomy** (the bank's monodromy over the turn, whose growth the comparison reads and whose
derivative in `ρ` the move pairs). The helix (the placed phases `P^(λ−c)`), the pair (each
crossing's contact with the ring) and the tower thread stay attached: nothing here changes a
phase, a contact or a restriction.

## 0. The recorded failures this work could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **5, an uncertified step.** The modulus's old unit move, `Δρ = slope⁺/γ_ρ`, gave one scalar the
  whole port's first-order descent, so its size ran inverse to its own slope; from a founding below
  one it carried the modulus back to one in two moves, its second carried target past one and held
  only by the passive bound (§1e). It is replaced by the least-squares step `−γ_ρ/G_ρ`, proportional
  to the slope with the storage curvature `G_ρ = Σ_c |∂z_c/∂ρ|²` read on the same contributions (Lean
  `modulus_least_squares`). Every commit guard stays: the passive bound `ρ ≤ 1`, `[ρ/2, 1]` a move,
  the lattice, the entry bound, admission, the Floquet certificate, the first order on the carried
  storage moves (the modulus's included) and the strict decrease by disjoint enclosures.
- **6, seen material graded as unseen.** The measurement read development seeds 32, 41, 42 and 43
  only; the confirmation seeds below (`2_026_093_021`–`026`) appear in no record, receipt, harness
  or log of any branch before this commit, and are read once each, after it.
- **7, a local pass read as progress.** The acceptance is whole sections on the fresh confirmation
  against both openings; `F`'s fall on training batches is reported beside it, never as success.
  Development reads that released no whole section are not read as a result.
- **9, a refusal answered with a larger limit.** Every run is projected from its development read
  and pinned with its deadline (§5); a run that reaches it is reported incomplete and not rerun; no
  guard is suspended (the outer process guard is the deadline plus 100 seconds).
- **Tuning a constant instead of deriving a law.** The founding modulus is not read from the
  landscape of §1b, which was measured first: it is the greatest lattice modulus whose one-turn
  transport carries a datum to one unit of the weights' chart, `ρ₀^d ≤ 2^(−L_ν)`, from the ring's
  declared period `d = 60` and the chart's declared grain `L_ν = 21` (§2a). No value of `ρ` was
  chosen by a run's releases, and no step size by a run's path: the least-squares step is the
  port's normal-law principle on the modulus's one feature.
- **2, a window.** At `ρ₀` every datum of the span enters with positive weight (Lean
  `framed_weight_pos`), and on the chart too: the farthest datum of the order-2 span, 47 ticks from
  a station, weighs `ρ₀^47` (between `2^(−17)` and `2^(−16)`) of the station's candidate, and over
  the span's mass (below `1/(1 − ρ₀) < 5`) more than `2^(−19)`, where the chart's half unit is
  `2^(−22)`.
- **4, a located cause carried unrepaired.** The located cause (the lossless founding, and the
  equal-share unit that returns the modulus to it) is repaired in its owners
  (`hnn::constitution`, `hnn::executed`). The consumers that do not read a modulus below one (the
  card, the bank's face path, the readout's one anchor, a passage over one turn) keep the lossless
  founding and refuse, typed, as before; nothing new is built on them.
- **1, an authored routine; 3, one construction across modalities.** Nothing names the order-2
  rule, a lag or a chain. The founding reads a ring's period and a chart's grain, which every
  modality's ring has; the step reads the storage's metric.
- **11, the programming language.** The law is a transport's modulus, its one-turn alias on the
  weights' chart and a least-squares fit of storage moves; batches and moves are its realization.

## 1. The deciding measurement: `γ_ρ` split by term kind

The owner's receipt now splits the modulus's slope (`hnn::executed::SlopeSplit`, `modulus_slopes`):
the terms led by the threshold (`−ln a_t`) and by a class rival (`ln(a_x/a_t)`), their counts,
`Σ (f)_+` and `γ_ρ` by the leading kind (their sum is `γ_ρ`); and, at every positive term, its two
parts read alone: the target's `−⟨ĝ_t, ∂z_t/∂ρ⟩` (the threshold branch) and its leading class
rival's `+⟨ĝ_x, ∂z_x/∂ρ⟩` (the class branch at every term is their sum). The composition has no
order term: the order is read beside `F`, never descended. A negative slope asks `ρ` upward. Every
value below is `·/4096` nats per unit of `ρ` (or nats, for `F`), an exact cell `[a, a + 1)` written
by its lower end; the receipts hold every line.

**1a. The opening at `ρ = 1`, four development batches of 8 order-2 requests.** Every term is
threshold-led (64 of 64 on each); nothing is past one, so the release holds all 8 requests.

| Seed | `F` | `γ_ρ` (all threshold-led) | the class rival's part alone | the class branch alone | `γ_ρ` at `63/64` |
|---|---|---|---|---|---|
| 41 | 353558 | **−645906** | −392777 | −1038682 | **+502694** |
| 32 | 377195 | **−370830** | +1562839 | +1192010 | **+189441** |
| 42 | 352645 | **−346322** | +21977 | −324344 | **−391227** |
| 43 | 385987 | **−314863** | +206917 | −107946 | **+119621** |

At the lossless opening the threshold carries the whole slope, negative on 4 of 4 batches: the
target's growth rises toward the lossless mixture. The class branch read alone is mixed (negative
on 3, positive on 1). By `63/64` the threshold-led slope points inward on 3 of 4. At one lattice
unit below one (seed 41, `2097151/2097152`) it is `−646370`, the boundary's.

**1b. The opening on seed 41 across moduli** (read, not chosen from):

| `ρ` | `F` | released of 8 | threshold-led / class-led terms | `γ_ρ` |
|---|---|---|---|---|
| 1 | 353558 | 0 | 64 / 0 | −645906 |
| `63/64` | 350044 | 0 | 64 / 0 | +502694 |
| `15/16` | 275698 | 0 | 64 / 0 | +2475940 |
| `7/8` | 362502 | 3 | 72 / 110 | +343071 (threshold-led +2943022, class-led −2599951) |
| `102837/131072` (the founding, §2a) | 850488 | 8 | 1 / 232 | −5281771 (class-led −5302264) |
| `3/4` | 1005623 | 8 | 0 / 227 | −3229066 |
| `5/8` | 1186620 | 8 | 0 / 231 | −1205626 |
| `1/2` | 1088485 | 8 | 0 / 214 | +633645 |
| `1/4` | 1082941 | 8 | 0 / 227 | +2494741 |

**The lossless modulus is a boundary local minimum of the comparison at the opening**: the slope
at one and one lattice unit below points outward (past the passive bound), and by `63/64` inward,
where `F` is already lower (`350044` against `353558`), and lower still at `15/16`, where the
release still holds. The certified move reads the first order at its point: at one the only
descending direction for the modulus is the forbidden one, so it never moves. Below `7/8` the release proceeds
(every request released, none whole) and the class-led terms carry the slope, upward: an unlearned
`E`'s contrasts are at chance, so every concentration on the candidate raises a rival, and a
released wrong section is compared at every refinement (`F` between 207 and 290 nats against
between 86 and 87 at one, where the release holds after one refinement).

**1c. Along `E`'s moves at `ρ = 1`** (the certified move from the lossless opening, seed 41, six
moves of 8; the modulus's unit move the old equal-share one):

| Move | `ρ` → | `γ_ρ` | threshold-led: terms, `γ` | class-led: terms, `γ` | the target's part | the class rival's part | the class branch alone | released |
|---|---|---|---|---|---|---|---|---|
| 0 | 1 | −645906 | 64, −645906 | 0 | −645906 | −392777 | −1038682 | 0 |
| 1 | 1 | −959949 | 64, −959949 | 0 | −959949 | +516131 | −443817 | 0 |
| 2 | 1 | −6738 | 64, −6738 | 0 | −6738 | −239413 | −246151 | 0 |
| 3 | `498593/524288` | +838727 | 56, +863312 | 26, −24586 | −188374 | −180851 | −369224 | 1 |
| 4 | `492997/524288` | +1673193 | 56, +2107069 | 29, −433877 | +3507136 | −3938405 | −431269 | 1 |
| 5 | `1967475/2097152` | +860260 | 48, +1833593 | 44, −973334 | +3905587 | −4905924 | −1000336 | 2 |

**`E`'s moves change the threshold's sign, not the class's**: after three moves of `E` the
threshold-led slope turns inward on this batch and the modulus leaves one; the class-led slope and
the class branch read alone stay outward at every move. On the pinned training's seed the modulus
never left one in 16 moves (the result record §4), and on the alternation's in 8: the escape
depends on the batch.

**1d. At trained constitutions, seed 41.**

| Constitution | `ρ` | `F` | released, whole | `γ_ρ` | split |
|---|---|---|---|---|---|
| the refit (§2a there, on the lattice) | `137573/262144` | 147481 | 8, 6 | **+223716** | class-led 69 of 69; the target's part +1173806, the rival's −950091 |
| the refit's `E` at one | 1 | 291255 | 0, 0 | −66700 | threshold-led 64 of 64; the class branch alone −562779 |
| the pinned native training's `E` | 1 | 25917 | 7, 0 | −1367329 | threshold-led 29 (−1033904), class-led 197 (−333425) |

The refit's point lies in a basin below one whose slope asks for lower `ρ`; read at one, the same
`E` is trapped as the opening is.

**1e. The float fit's first steps, and the founding under the equal-share unit.**
- The float fit (`eP_rho_path.py order2 400 24 256 41 0.03 0.05 1 16`, the pinned protocol's
  parameters, its own draws) **does not move `E` first**. Its softmax's slope in `ρ` asks `ρ` down
  at step 0, and Adam's sign-normalized step moves `ρ` by `1/20` at once (1 to `19/20`), over the
  rise the certified move cannot cross; over 24 steps the slope's sign alternates (13 inward, 11
  outward) and `ρ` settles between `6/7` and `7/8`, while `E`'s largest entry grows from `1/2` to
  between 1 and `11/10` by at most `3/100` a step. The float fit left one by a step that does not
  scale with its slope.
- **From the founding (§2a) under the equal-share unit** (seed 41, three moves): the modulus went
  `102837/131072` → `1766555/2097152` → 1 (the second move's carried target past one, held by the
  passive bound) → 1, the release holding all 8 at the third move; `F` fell by holding.

**What the measurement decides.** Candidate (b), the threshold's composition with the class terms,
is not what holds the modulus: at the lossless opening the threshold is the only leading branch,
but the class branch read alone also points outward on 3 of 4 batches, and after `E` moves the
threshold is what turns inward while the class stays outward. A recomposition cannot take the
modulus off one at the opening. Two causes are measured: **the founding sits on a boundary local
minimum** (1a, 1b), and **the modulus's unit move runs inverse to its slope**, so a founding off one
is carried straight back (1e).

## 2. The law [agent-inferred, from §1]

**2a. The founding off the lossless boundary** (`Constitution::founding_transport`; Lean
`HNN/IndexedOpen` §6). The modulus one is the passive set's boundary and the law's degenerate
point, as the standing's node was (the [fold record](2026-09-29_THE_STANDINGS_FOLD_THE_COPY_AND_THE_MOIRE_RETURN_AND_TEXT_TURNS_ITS_SHEETS_BY_THE_LOCK.md):
founding on the node was the defect, and the law founded off it): no recency is marked
(`lossless_term_modulus`), and a datum a whole turn farther weighs what the nearer does
(`lossless_alias`). The phase record carries a datum's age only within one turn, so its one-turn
alias weighs `ρ^d` of the nearer datum (`founded_modulus_alias`). The transport is founded at **the
greatest modulus on the source port's lattice whose one-turn transport carries a datum to one unit
of the weights' chart**:

```text
ρ₀ = k 2^(−L_s),   k^d 2^(L_ν) ≤ (2^(L_s))^d < (k + 1)^d 2^(L_ν)     (Lean IsFounding)
ρ₀^d ≤ 2^(−L_ν)                                                     (founded_modulus_pow_le)
τ_b + d = τ_a ≤ τ_j  ⇒  w_j(b) = ρ₀^d w_j(a) ≤ 2^(−L_ν) w_j(a)       (founded_modulus_alias_le)
L_ν ≥ 1 ⇒ ρ₀ < 1;   L_ν ≤ L_s d ⇒ ρ₀ > 0                              (founded_modulus_lt_one, _pos)
order-2: d = 60, L_ν = L_s = 21  ⇒  ρ₀ = 1645392/2^21 = 102837/131072  (order_founding)
```

`d` is the ring's declared period, `L_ν` the population chart's exponent (the grain the weights are
read on), `L_s` the source port's lattice. Its reasons: it is the least dissipative transport under
which the ring's one-turn phase record reads the transport at the chart's grain (retention is a
quotient sufficient for the admitted future: what the record cannot tell apart weighs at most one
chart unit); it reads only the declaration, nothing of a terrain; and it lies inside the passive
set, off the boundary where the certified move cannot act. The founding applies where the executed
comparison reads the transport (the bank's release, the declared opening of its training); the card,
the face path, the readout's one anchor and a passage over one turn keep one and refuse a modulus
below it, typed, until their forms are built.

**2b. The modulus's least-squares step** (`hnn::executed`, "The modulus's unit move is its
least-squares step"; Lean `HNN/ExecutedComparison` §6). The port's normal law fits its storage moves
`ΔE f` to the proposal's descent covectors in least squares. The modulus has one feature, each
contribution's storage derivative `v_c = ∂z_c/∂ρ` read from its station; its unit move is the same
fit:

```text
Δρ = −γ_ρ / G_ρ,   γ_ρ = Σ_c sign_c ⟨ĝ_c, v_c⟩,   G_ρ = Σ_c |v_c|²      (modulus_least_squares)
γ_ρ Δρ = −γ_ρ²/G_ρ ≤ 0                                                (modulus_least_squares_descends)
none upward from ρ = 1;  ρ + ηΔρ held in [ρ/2, 1] on the lattice;  η the ladder's, shared with E
```

It retires the equal-share unit `Δρ = slope⁺/γ_ρ` (§1e). The ladder, its depth, its start at the
first-order zero of `F` (now read on the joint first order `slope + γ_ρΔρ`) and every commit guard
are unchanged.

**What the law does not repair** [agent-inferred]. At the founding the class-led slope points
outward (§1b): an unlearned `E` asks for less contrast. Under the least-squares step the modulus
drifts upward slowly while `E` moves (§5: by `13931/1048576`, less than `1/64`, over three
development moves), and
turns only when `E`'s class contrasts are right (the refit's `+223716`). **The expected blocker**:
that 16 moves of 8 do not teach `E` the order-2 relation at `ρ` near `ρ₀`; the secondary cause the
refit showed (a lag-1 neighbour read in place of the seed) is unrepaired.

## 3. What is built (`6dc1e5ae`)

- `hnn::constitution`: `founding_modulus`, `Constitution::{founding_transport, founded_transport}`.
- `hnn::executed`: `modulus_normal` (`γ_ρ` and `G_ρ`), the least-squares unit, the joint first order;
  `ExecutedMove::{modulus_curvature, modulus_unit, split}`; `SlopeSplit`, `TermKind`,
  `modulus_slopes`.
- `hnn::moment`: the founding's law in the header.
- Lean `HNN/IndexedOpen` §6 (`founded_modulus_alias`, `founded_modulus_alias_le`, `lossless_alias`,
  `IsFounding`, `founded_modulus_pow_le`, `founded_modulus_greatest`, `founded_modulus_lt_one`,
  `founded_modulus_pos`, `order_founding`) and `HNN/ExecutedComparison` §6 (`ray_sum_sq`,
  `modulus_least_squares`, `modulus_least_squares_descends`); standard axioms only.
- Tests: `the_transport_is_founded_off_the_lossless_boundary` (the founding's arithmetic at
  `(21, 60, 21)` and `(21, 35, 21)`, maximality, the owner on the joint field, the refusal off a
  source ring); `the_committed_move_carries_the_transport_modulus` now holds the unit to `−γ_ρ/G_ρ`,
  its share negative, and the adopted trial's carried modulus to the lattice's nearest of
  `ρ + ηΔρ`.
- The harness: the executed arm's declared opening is founded (`founded_opening`; `@ρ` on an arm or
  a label reads another modulus, `lossless` the old opening), `executed slopes`, the split printed on
  every move; `eP_rho_path.py`.
- Atlas `hnn.transport-founding`; `hnn.executed-move` and `hnn.transport-modulus` restated.
- Gates at `6dc1e5ae`: `cargo check --workspace --all-targets` clean; `cargo test -p holonics --lib`
  975 passed; `bash tools/lean_check.sh Holonics HolonicsResearch` 10,251 jobs, no `sorry`.

## 4. The acceptance, fixed before any measured run

The runs use the build `6dc1e5ae` and the harness `hnn_prediction -- executed`, one at a time on
the host's cores.

1. **Every exact check holds**, every guard a commit guard: on every read release every lock
   certified and no refused certificate; every adopted move holds every guard (printed); the gates
   of §3.
2. **The native certified training from the founded opening keeps the modulus below one**:
   `executed train executed-open order2 2026093021 8 16 <deadline> <out>` (16 moves of 8 fresh
   requests at training seed `2_026_093_021`, the opening `E₀` with `ρ₀ = 102837/131072`). Reported
   per move: the modulus, `γ_ρ` and its split, `G_ρ`, the unit, `F` before and after, the batch's
   releases. Holds when every adopted modulus is below one.
3. **Order-2 is read on fresh confirmation**: `executed evaluate order2 2026093022 128 <out>
   lossless opening executed-open=<E>` (128 requests at seed `2_026_093_022`; the lossless opening
   `E₀, ρ = 1`, the founded opening `E₀, ρ₀`, the trained constitution). **Passes** when the trained
   constitution releases strictly more whole sections than both openings, with item 1 holding.
   Reported beside: the station-framed result's 0 of 128 (the lossless training on the spent seeds)
   and the refit's 96 (Stage 0's held-out draw, a float fit read natively); the first
   request-dependent locks kept separate (the first lock at station 0 or 1, and whether it is right),
   and the first lock right overall; holds, incorrect releases, stations right by station, the
   trained `ρ`; the complete synthetic outputs.
4. **Regressions**: the same arm, 8 moves of 8 from the founded opening, on the alternation
   (training `2_026_093_023`, confirmation `2_026_093_024`) and the line (`2_026_093_025`,
   `2_026_093_026`), 128 requests each, read at the lossless opening, the founded opening and the
   trained constitution. Each passes with no fewer whole sections than the better of its two
   openings. Reported beside the station-framed result's 19 and 15 (on the spent seeds, other
   requests: not the same test).
5. **Time and memory** (§5): every run within its deadline and a resident set of 4 GB; a run past
   its deadline is reported incomplete, never rerun with a larger one; no guard suspended.

## 5. The development read and the projections

Three moves under the law from the founded opening on development seed 41
(`law_path_dev41.txt`): the modulus `102837/131072` → `1652961/2097152` → `831267/1048576` →
`836627/1048576` (the unit move `[1892, 1893)/65536`, `[1196, 1197)/65536`, `[669, 670)/65536`
at steps `1/8`, `1/4`, `1/2`; `G_ρ` between `168591828/4096` and `191484336/4096`); `F` fell
`850488/4096` → `742022/4096`, `670079/4096` → `490826/4096`, `558473/4096` → `393022/4096`;
releases 8, 8, 6 of 8, none whole; 153,917, 199,329 and 196,139 ms a move, peak resident
263,671,808 bytes. Every batch releases from the founding, so every move reads every refinement.

| Run | Projection | Deadline (the outer guard 100 s past it) |
|---|---|---|
| order-2 training, 16 moves of 8 | 2,400,000–4,800,000 ms | 6,000,000 ms |
| order-2 confirmation, 3 × 128 | 800,000–1,500,000 ms | 2,400,000 ms |
| alternation and line training, 8 moves of 8 each | 1,200,000–2,400,000 ms each | 3,000,000 ms each |
| their confirmations, 3 × 128 each | 800,000–1,500,000 ms each | 2,400,000 ms each |

## 6. What is expected, and the falsifiers [agent-inferred]

- **Training**: the modulus drifts upward from `ρ₀` while the class-led slope is outward and stays
  below one (the least-squares unit moves it by a few hundredths a move at most); `F` falls on
  fresh batches.
- **Confirmation**: the founded opening releases every order-2 request, none whole (§1b's batches:
  0 of 32 whole); whether 16 moves teach `E` the relation is the test.

**Falsifiers:**
- the trained modulus returns to one (the founding does not hold under the least-squares step);
- training improves and untouched confirmation does not (whole sections not above both openings);
- a regression releases fewer whole sections than its better opening;
- an adopted move fails a guard, or a read release refuses a certificate;
- a resource bound is reached.

## 7. Owed in #62

"The modulus founded off one" (September 30; `hnn::constitution::{founding_modulus,
Constitution::founding_transport}`, `hnn::executed`'s least-squares unit; Lean `HNN/IndexedOpen` §6
proves the founding's arithmetic, maximality, bounds, the alias bound and the order-2 instance, and
`HNN/ExecutedComparison` §6 the least-squares step and its descent):
1. **The owner's root is the founding**: that `BigUint::nth_root` of `2^(L_s d − L_ν)` is the `k` of
   `IsFounding` (held by the owner's test on instances).
2. **The phase record's sufficiency at the founding**: that per-phase counts decayed at the founding
   modulus read a passage of any length within one chart unit of its transported weights (the leaky
   count, owed since the passage law), so the one-turn refusal (`AliasedAges`) can lift at `ρ₀`.
3. **The modulus's statistic**: the port's normal law carries its Gram across moves; the modulus's
   least-squares step reads one batch's `G_ρ`. Its carried form, or the statement that the batch's
   suffices, is owed.
4. **The founding on the other consumers**: the card's open, the face path's shared resonance and
   the readout's station-framed anchor below one (each refuses it now).
