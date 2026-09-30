# The modulus founded off one, measured: the modulus stays below one, and order-2 training learns the lag-1 copy

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
runs under the [pin](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md) (`3f4e3321`,
at the build `6dc1e5ae`), and for the section counts after them; [proved-derived; formal-checked]
for Lean `HNN/IndexedOpen` §6 and `HNN/ExecutedComparison` §6; [agent-inferred] where marked.

**Occasion.** The station-framed placement's result left the modulus at one on every native move.
The pin read `γ_ρ` split by term kind (its §1: at the lossless opening every term is
threshold-led and the slope points outward on 4 of 4 development batches; one is a boundary local
minimum; from a founding below one the old equal-share unit returned the modulus to one in two
moves), derived the law (the transport founded at the greatest lattice modulus with
`ρ₀^d ≤ 2^(−L_ν)`, `102837/131072` for order-2; the modulus moved by its least-squares step
`−γ_ρ/G_ρ`), and fixed the acceptance on fresh seeds `2_026_093_021`–`026`. The runs went once, one
at a time. The orchestrator stopped the line's confirmation before its trained constitution was read
(a course correction, not a deadline; §4).

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches the tube (the
span's transport and its founding), faces and placement (each datum's weight from its station) and
the cell holonomy (the bank's monodromy, whose growth the comparison reads); the helix, the pair and
the tower thread stay attached.

## 0. The recorded failures this work could repeat, and how each was held

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **5, an uncertified step.** Every one of the 32 adopted moves held every commit guard (the
  passive bound, `[ρ/2, 1]`, the lattice, the entry bound, admission, the Floquet certificate, the
  first order on the carried storage moves, the strict decrease by disjoint enclosures); no read
  release refused a certificate. The modulus moved only by its least-squares step, proportional to
  its slope.
- **6, seen material graded as unseen.** The confirmation seeds were read once each, after the pin;
  the development seeds of the pin's §1 were not reused.
- **7, a local pass read as progress.** `F` fell on the fresh training batches and is reported
  beside the acceptance, not as it. The alternation passes its pinned criterion, and every one of
  its whole sections is a constant request, which a lag-1 copy completes; §3 says so.
- **9, a refusal answered with a larger limit.** Every completed run within its deadline; nothing
  rerun; the stopped confirmation is reported incomplete, not rerun.
- **Tuning a constant.** The founding was derived from the ring's period and the chart's grain
  before any pinned run and was not changed after; no step size was chosen from a run.
- **11, the programming language.** Read as a transport's modulus, its one-turn alias and a
  least-squares fit of storage moves.

## 1. The law (the pin's §2, built at `6dc1e5ae`)

```text
ρ₀ = k 2^(−L_s),  k^d 2^(L_ν) ≤ (2^(L_s))^d < (k + 1)^d 2^(L_ν)   order-2: d = 60, L_ν = L_s = 21, ρ₀ = 102837/131072
Δρ = −γ_ρ / G_ρ,  G_ρ = Σ_c |∂z_c/∂ρ|²,  γ_ρΔρ = −γ_ρ²/G_ρ ≤ 0,  none upward from ρ = 1
```

Lean `HNN/IndexedOpen` §6 (`IsFounding`, `founded_modulus_pow_le`, `founded_modulus_greatest`,
`founded_modulus_lt_one`, `founded_modulus_pos`, `founded_modulus_alias`, `founded_modulus_alias_le`,
`lossless_alias`, `order_founding`) and `HNN/ExecutedComparison` §6 (`ray_sum_sq`,
`modulus_least_squares`, `modulus_least_squares_descends`); standard axioms only.

## 2. Training (pinned items 1 and 2)

**Order-2** (`executed train executed-open order2 2026093021 8 16 6000000`: 16 moves of 8 fresh
requests from the founded opening). Every move adopted, 0 refused, 23,040 readings; every value
`·/4096` (nats, or nats per unit of `ρ`), an exact cell written by its lower end.

| Move | The modulus after | `F` before → after | `γ_ρ` | class-led terms | threshold-led terms | `G_ρ` | unit `·/65536` | released, whole, stations right (of 64) |
|---|---|---|---|---|---|---|---|---|
| 0 | `1651371/2097152` | 875694 → 626985 | −4062840 | 235 | 3 | 178127631 | 1494 | 8, 0, 12 |
| 1 | `206811/262144` | 508179 → 504560 | −2011168 | 216 | 0 | 169139639 | 779 | 8, 0, 16 |
| 2 | `829393/1048576` | 607016 → 406252 | −3071995 | 218 | 17 | 187385198 | 1074 | 7, 0, 11 |
| 3 | `1663219/2097152` | 411761 → 371162 | −818995 | 228 | 2 | 193727828 | 277 | 8, 0, 10 |
| 4 | `1668609/2097152` | 368362 → 303765 | −951032 | 223 | 8 | 185010714 | 336 | 8, 0, 14 |
| 5 | `837081/1048576` | 406429 → 260677 | −2120790 | 224 | 0 | 200217601 | 694 | 8, 0, 16 |
| 6 | `840071/1048576` | 296550 → 254355 | −1101980 | 232 | 0 | 193224429 | 373 | 8, 0, 10 |
| 7 | `422723/524288` | 300958 → 278118 | −2088037 | 227 | 1 | 203668715 | 671 | 8, 0, 12 |
| 8 | `424979/524288` | 278906 → 237505 | −3103999 | 214 | 0 | 180349006 | 1127 | 8, 0, 17 |
| 9 | `851985/1048576` | 186518 → 169151 | −676506 | 212 | 0 | 174974087 | 253 | 8, 0, 15 |
| 10 | `1710639/2097152` | 180411 → 165846 | −1193637 | 223 | 0 | 187675860 | 416 | 8, 0, 15 |
| 11 | `1711193/2097152` | 166817 → 163707 | −1574413 | 206 | 0 | 186136832 | 554 | 8, 0, 15 |
| 12 | `107749/131072` | 183403 → 170030 | −2370254 | 221 | 0 | 194315333 | 799 | 8, 0, 19 |
| 13 | `1732429/2097152` | 156231 → 152763 | −783145 | 192 | 0 | 194484780 | 263 | 8, 0, 17 |
| 14 | `1739417/2097152` | 182681 → 126697 | −1591037 | 231 | 0 | 238740275 | 436 | 8, 0, 11 |
| 15 | `1750365/2097152` | 195097 → 148069 | −1099056 | 236 | 0 | 210521401 | 342 | 8, 0, 10 |

**Item 2 holds**: every adopted modulus lies below one; the modulus drifted from `102837/131072`
to `1750365/2097152` (between `5/6` and `21/25`). The slope asked the modulus upward on all 16
moves, carried by the class-led terms (at every move the class rival's part read alone outweighs
the target's: at move 15 `−12778933` against `+11679876`). `F` fell on every fresh batch at its
first reading, from `875694/4096` at move 0 to between `156231/4096` and `195097/4096` over the
last four; the training batches' releases stayed at no whole section and 10 to 19 of 64 stations
right, about the quarter a guess reads.

**The alternation** (training `2_026_093_023`, 8 moves of 8): 8 adopted, 0 refused; the modulus
`102837/131072` → `1670477/2097152`, `γ_ρ` negative on all 8 moves; batch whole sections
2, 0, 1, 1, 0, 3, 0, 3. **The line** (training `2_026_093_025`, 8 moves of 8): 8 adopted, 0
refused, complete (1,496,629 ms, exit 0); the modulus `102837/131072` → `840009/1048576`; `γ_ρ`
negative on moves 0 to 6 and positive, inward, at move 7 (`+337069/4096`, the unit
`−157/65536`); batch whole sections 0, 0, 0, 0, 1, 1, 1, 0.

## 3. Confirmation (pinned items 3 and 4)

Each constitution generates every request from the open section; no refused certificate in any
read release.

| Terrain, seed | Constitution | Released / held | **Whole** | Incorrect | Reaching the termination | Stations right (of 1,024) | By station | First lock at station 0 or 1 (of them right) | First lock right |
|---|---|---|---|---|---|---|---|---|---|
| order-2, `…022` | lossless (`E₀`, `ρ = 1`) | 0 / 128 | **0** | 0 | 32 | 243 | 40 27 27 31 31 30 21 36 | 0 (0) | 0 |
| order-2 | the founded opening (`E₀`, `ρ₀`) | 121 / 7 | **0** | 121 | 15 | 197 | 23 18 27 25 33 27 26 18 | 1 (0) | 26 |
| order-2 | trained (`ρ = 1750365/2097152`) | 128 / 0 | **0** | 128 | 0 | 263 | 31 22 35 34 43 42 36 20 | 46 (6) | 28 |
| alternation, `…024` | lossless | 6 / 122 | **6** | 0 | 0 | 350 | 60 40 47 47 38 37 38 43 | 0 (0) | 6 |
| alternation | the founded opening | 121 / 7 | **6** | 115 | 0 | 274 | 58 42 38 39 25 27 25 20 | 12 (12) | 20 |
| alternation | trained (`ρ = 1670477/2097152`) | 128 / 0 | **22** | 106 | 0 | 530 | 64 94 67 73 58 58 50 66 | 50 (50) | 96 |
| line, `…026` | lossless | 11 / 117 | **11** | 0 | 33 | 306 | 28 31 36 44 28 38 42 59 | 0 | 11 |
| line | the founded opening | 122 / 6 | **11** | 111 | 7 | 264 | 33 53 23 61 21 34 16 23 | 11 | 23 |
| line | trained (`ρ = 840009/1048576`) | **not read: the run was stopped by the orchestrator** | | | | | | | |

- **Order-2 fails its acceptance**: the trained constitution releases 0 whole sections of 128
  against 0 for both openings; stations right 263 of 1,024, a quarter read by chance being 256.
  Beside the station-framed result's 0 (the lossless training, other requests) and the refit's 96
  (a float fit read natively on Stage 0's held-out draw).
- **The alternation passes its pinned criterion** (22 whole against 6 and 6). **Every one of the 22
  is a constant request** (`a = b`, 30 of the 128 requests); of the 98 alternating requests none is
  whole for any constitution. The six whole sections of each opening are constant requests too.
- **The line is incomplete**: its training completed all 8 moves; its confirmation read the two
  openings (11 and 11 whole) and was stopped while reading the trained constitution, so no line
  result exists and no section listing was written.

**What the trained constitutions release** (every released section, `eM_section_shapes.py`):

| Terrain | Constitution | Released classes 0 / 1 / 2 / 3 / termination | Adjacent stations equal (a lag-1 copy) | Stations following the terrain's rule among the section's own | Sections following it throughout |
|---|---|---|---|---|---|
| order-2 | the founded opening | 145 / 381 / 127 / 304 / 11 | 184 of 847 | 41 of 726 | 0 |
| order-2 | trained | 249 / 176 / 10 / 589 / 0 | **532 of 896** | 91 of 768 | 0 |
| alternation | the founded opening | 233 / 385 / 121 / 229 / 0 | 148 of 847 | 531 of 726 | 38 |
| alternation | trained | 333 / 121 / 137 / 433 / 0 | **657 of 896** | 561 of 768 | 22 |

The trained order-2 constitution continues a station by its lag-1 neighbour (532 of 896 adjacent
pairs equal, against 184 of 847 at its opening; the rule needs adjacent stations unequal) and
favours class 3 (589 of 1,024 stations) over class 2 (10). Its sections follow the rule at 91 of
768 stations, below the 192 a guess reads.

**The synthetic outputs** (order-2, the trained constitution, the first 16 of 128; all 128 of every
read constitution, order-2 and the alternation, in the receipts' section listings):

| Last four request cells | Target | Released | Lock order |
|---|---|---|---|
| 0 0 3 3 | 0 0 1 1 2 2 3 3 | 3 1 0 0 0 1 2 0 | 7 6 4 0 1 3 2 5 |
| 2 3 3 0 | 0 1 1 2 2 3 3 0 | 0 0 0 0 0 1 3 3 | 7 3 6 5 0 1 4 2 |
| 2 3 1 0 | 2 1 3 2 0 3 1 0 | 0 0 1 3 3 3 3 2 | 7 0 1 6 5 4 3 2 |
| 3 1 3 0 | 0 1 1 2 2 3 3 0 | 3 3 3 1 3 3 1 3 | 5 6 4 7 2 3 1 0 |
| 2 3 0 1 | 1 2 2 3 3 0 0 1 | 3 3 3 3 0 0 0 0 | 3 2 1 5 0 7 4 6 |
| 2 0 2 1 | 3 2 0 3 1 0 2 1 | 3 3 3 3 1 0 0 3 | 2 7 1 0 5 3 4 6 |
| 1 0 3 0 | 0 1 1 2 2 3 3 0 | 0 0 0 3 3 1 3 3 | 7 1 2 6 4 5 0 3 |
| 1 1 3 2 | 0 3 1 0 2 1 3 2 | 3 3 1 3 3 1 3 3 | 0 4 3 5 7 1 2 6 |
| 3 0 2 2 | 3 3 0 0 1 1 2 2 | 3 1 3 3 3 1 0 0 | 3 2 0 7 6 5 4 1 |
| 3 0 2 3 | 3 0 0 1 1 2 2 3 | 3 3 3 1 3 3 1 3 | 2 3 1 5 4 6 7 0 |
| 1 1 2 3 | 3 0 0 1 1 2 2 3 | 3 1 3 3 3 3 1 0 | 0 5 6 4 3 1 7 2 |
| 1 0 3 2 | 0 3 1 0 2 1 3 2 | 3 3 1 3 3 1 3 3 | 3 4 0 5 6 7 1 2 |
| 0 2 2 3 | 3 0 0 1 1 2 2 3 | 3 3 3 3 1 0 0 0 | 1 2 6 5 0 7 3 4 |
| 1 3 0 2 | 1 3 2 0 3 1 0 2 | 3 1 3 3 3 3 1 0 | 3 4 7 6 5 2 1 0 |
| 2 3 0 3 | 1 0 2 1 3 2 0 3 | 3 3 3 3 1 0 0 0 | 1 2 0 7 6 3 4 5 |
| 3 0 1 3 | 2 0 3 1 0 2 1 3 | 3 3 3 1 3 3 3 1 | 2 1 5 3 6 7 0 4 |

No released section follows the rule. The alternation's trained releases, the first 16, likewise:
the four whole ones are `2 2 2 2 2 2 2 2`, `0 0 0 0 0 0 0 0`, `2 2 2 2 2 2 2 2` and
`0 0 0 0 0 0 0 0`; the alternating requests come back as runs (`3 3 0 3 3 3 3 3` for
`1 3 1 3 1 3 1 3`, `0 0 0 0 2 2 2 2` for `0 1 0 1 0 1 0 1`).

## 4. The falsifiers, read as written

- **The trained modulus returns to one: does not fire.** It stayed below one on every move of all
  three trainings.
- **Training improves and untouched confirmation does not: fires on order-2.** `F` fell on every
  fresh batch; the confirmation reads 0 whole sections against 0 and 0.
- **A regression releases fewer whole sections than its better opening: does not fire on the
  alternation** (22 against 6); **not read on the line** (its confirmation stopped).
- **An adopted move fails a guard, or a read release refuses a certificate: does not fire.**
- **A resource bound is reached: does not fire** (§6). The line's confirmation was stopped by the
  orchestrator, not by its deadline.

## 5. The verdict and what the measurement located [measured; agent-inferred where marked]

- **Built and exact**: the founding off the lossless boundary and the least-squares step in their
  owners, the slope split on the receipt, Lean `HNN/IndexedOpen` §6 and `HNN/ExecutedComparison` §6.
- **Acceptance 1 holds** (every guard, every certificate, the gates of §7). **Acceptance 2 holds**
  (the modulus below one throughout). **Acceptance 3 fails** (order-2: 0 whole against 0 and 0).
  **Acceptance 4**: the alternation passes (22 against 6, all 22 constant requests); the line is
  incomplete. **Acceptance 5 holds** for every completed run.
- **The modulus is no longer the blocker.** Held below one, the certified move still does not teach
  `E` the order-2 relation in 16 moves of 8: it teaches the lag-1 copy (the secondary cause the
  station-framed refit showed, a neighbour one tick away read in place of the seed two ticks back,
  now the trained behaviour) and a preference for class 3, while `F` falls on the batches it moves.
- **The blocker, by its measurement** (the unicity record's two counts,
  [record](2026-09-30_UNICITY_THE_READINGS_LEAVE_ONE_KEY_AND_THE_HELIXS_CELLS_ARE_THE_FAREY_SEQUENCE.md)
  §5): order-2's key family (lag at most 40, a map of `ℤ/4`, `2¹¹·5` keys) can be pinned in 7
  readings (`n*_terrain`), and 1,024 rule steps (128 training requests) did not lock it
  (`n*_machine` above 1,024). [agent-inferred, named there, not designed here] Two candidate causes:
  the deposits are far below what the comparison hears (the certified step moves `E` by `[2⁻⁹, 2⁻⁸)`
  a deposit, a lock needs `2⁷` to `2⁹` times that), and the comparison is read past threshold,
  where the lock is already decided and a reading carries little about the key (every order-2
  training batch here released 7 or 8 of its 8 requests, from the founding on). That is the next loop's subject, not the modulus.

## 6. Time and memory

| Run | Measured ms | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| order-2 training, 16 moves | 3,533,424 | 2,400,000–4,800,000 / 6,000,000 | 268,255,232 |
| order-2 confirmation, 3 × 128 | 749,108 | 800,000–1,500,000 / 2,400,000 (below the projection) | 115,703,808 |
| alternation training, 8 moves | 1,318,739 | 1,200,000–2,400,000 / 3,000,000 | 267,595,776 |
| alternation confirmation, 3 × 128 | 717,557 | 800,000–1,500,000 / 2,400,000 (below the projection) | 112,189,440 |
| line training, 8 moves | 1,496,629 | 1,200,000–2,400,000 / 3,000,000 | 257,773,568 |
| line confirmation | **stopped by the orchestrator** after the two openings | 800,000–1,500,000 / 2,400,000 | not printed |

One at a time on the host's cores; no run reached its deadline.

## 7. Owed in #62

"The modulus founded off one" (September 30; `hnn::constitution::{founding_modulus,
Constitution::founding_transport, Constitution::founded_transport}`, `hnn::executed`'s least-squares
unit; Lean `HNN/IndexedOpen` §6 proves the founding's arithmetic, maximality, bounds, the one-turn
alias bound and the order-2 instance, and `HNN/ExecutedComparison` §6 the least-squares step and its
first-order descent):
1. **The owner's root is the founding**: that `BigUint::nth_root` of `2^(L_s d − L_ν)` is the `k` of
   `IsFounding` (held by the owner's test on instances).
2. **The phase record's sufficiency at the founding**: per-phase counts decayed at the founding
   modulus read a passage of any length within one chart unit of its transported weights (the leaky
   count), so the one-turn refusal (`AliasedAges`) can lift at `ρ₀`.
3. **The modulus's statistic**: the port's normal law carries its Gram across moves, the modulus's
   step reads one batch's `G_ρ`; its carried form, or the statement that one batch's suffices.
4. **The founding on the other consumers**: the card's open, the face path's shared resonance and
   the readout's station-framed anchor below modulus one (each refuses it now).

## 8. Commits and gates

- `6dc1e5ae`: the law in its owners, the Lean, the tests, the harness, the atlas rows.
- `3f4e3321`: the pin, with the deciding measurement's receipts.
- `4752db0b`: main at `adc05942` (unicity) merged; the records README's union.
- This record's commit: the record, the runs' receipts, `eM_section_shapes.py`, the records route,
  THE_REBUILD's entry.

Gates: at `6dc1e5ae`, `cargo check --workspace --all-targets` clean, `cargo test -p holonics --lib`
975 passed, `bash tools/lean_check.sh Holonics HolonicsResearch` 10,251 jobs, no `sorry`; after the
merge of `adc05942` (`4752db0b`), the same three: clean, 975 passed, 10,252 jobs with no `sorry`
(the merge added `Foundation/Unicity`; no Rust source changed since). The card suite was not
run: the card crate did not change, and the card refuses a modulus below one.

The receipts (`2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/`, synthetic terrain only): the pin's
development reads (the slopes, the lossless path, the equal-share path from the founding, the law's
path, the float fit's first steps, the refit on the lattice); every training log and trained
constitution; the order-2 and alternation confirmations' logs and complete section listings; the
line confirmation's log as far as it ran.
