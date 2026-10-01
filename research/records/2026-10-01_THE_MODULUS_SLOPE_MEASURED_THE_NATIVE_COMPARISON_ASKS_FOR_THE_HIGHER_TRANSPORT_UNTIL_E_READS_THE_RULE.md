# The modulus's slope measured: the native comparison asks for the higher transport until `E` reads the rule

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured], read once
under the [pin](2026-10-01_THE_MODULUS_SLOPE_PINNED_BEFORE_ITS_RUN.md) (`6800536d`);
[agent-inferred] where marked. Read-only: no move, no update. The only library change is a receipt
field, the storage curvature `G_ρ` on `SlopeSplit`.

The computational object is the helical pair interaction. Of the winding guide's objects this touches
**the tube** (the source passage's transport modulus) and **faces and placement** (the decision
terms). The rest stay attached.

## 1. The read

Gate A's batch (order-2, development seed `2_026_093_061`, 8 requests) and gate A's comparison (the
lock face at the decisions). At each constitution the proposal is formed exactly as `executed_move`
forms it, and its modulus part is read. `γ_ρ` is the composition's first-order slope in `ρ`, so
`γ_ρ < 0` asks for the higher transport. The unit move is the committed move's least-squares step
`−γ_ρ/G_ρ`. The chord from `ρ₀` to `ρ*` is `−544808/2^21`.

| Constitution | `ρ` (`/2^21`) | `L` (nats) | Right of 64, whole | `γ_ρ` (`/4096`) | Target part | Rival part | Unit move (`/2^21`) |
|---|---|---|---|---|---|---|---|
| `opening` (gate A's c0) | 1645392 | `[500197/4096, …)` | 15, 0 | **`[−332395, −332394)`** | `[3427139, …)` | `[−3759535, …)` | `[+2506, +2507)` |
| `gateA-c1` | 1646645 | `[517184/4096, …)` | 16, 0 | **`[−758991, −758990)`** | `[4015248, …)` | `[−4774240, …)` | `[+6091, +6092)` |
| `gateA-c2` | 1649691 | `[440147/4096, …)` | 15, 0 | **`[−527711, −527710)`** | `[3494744, …)` | `[−4022455, …)` | `[+4445, +4446)` |
| `chord-1/2` | 1372988 | `[375687/4096, …)` | 23, 0 | `[+169553, +169554)` | `[2927727, …)` | `[−2758175, …)` | `[−2753, −2752)` |
| `chord-3/4` | 1236786 | `[339158/4096, …)` | 25, 0 | `[−802179, −802178)` | `[1532063, …)` | `[−2334242, …)` | `[+18108, +18109)` |
| `refit-founded` (`E*` at `ρ₀`) | 1645392 | `[310210/4096, …)` | 22, 0 | `[+1617648, +1617649)` | `[5191364, …)` | `[−3573717, …)` | `[−9692, −9691)` |
| `refit` (`Θ*`) | 1100584 | `[133292/4096, …)` | 55, 5 | `[+65333, +65334)` | `[402495, …)` | `[−337162, …)` | `[−1904, −1903)` |

Every term is class-led, as every lock-face term is.

**The identity controls hold.** `opening`, `gateA-c1` and `gateA-c2` reproduce gate A's
constitutions 0, 1 and 2 in `L`, solved count and stations right. Their unit moves are gate A's
actual modulus changes at its adopted steps: `+1253 = ½ · 2506` at move 0 (`η = 1/2`), `+3046`
from `6091` at move 1 (`η = 1/2`), and `+8892 = 2 · 4446` at move 2 (`η = 2`). So the read is the
move's own modulus part.

## 2. Against the outcome rules

- **(S) holds: a sign obstruction.** `γ_ρ < 0` at all three of gate A's constitutions. Wherever
  gate A stood, its own comparison asked for the higher transport, so its moves raised `ρ` or
  wandered (net `+3531/2^21` over 16 moves).
- **(K) does not hold at gate A.** It also fails where the sign is right. With the refit's `E`, the
  comparison asks for the lower transport at `ρ₀`, but its unit move is `−9692/2^21`, which is
  `136202/2423` (between 56 and 57) unit moves short of the chord. At `chord-1/2` that count is
  `544808/2753` (between 197 and 198). Any repair of the sign therefore still has to move the
  modulus far faster than this least-squares step does.
- **Along the chord** the sign runs `−, +, −, +` (opening, `chord-1/2`, `chord-3/4`, refit). It is
  positive at `refit-founded`, which agrees with the segment probe's secant: with `E*`, lowering `ρ`
  from `ρ₀` descends, locally and over the whole leg. It is negative at `chord-3/4`, where the
  chord's strict descent comes from its `E` part.
- **The split.** The target part always asks for the lower transport (positive), and the rival
  part always for the higher (negative). The sign is whichever is larger.
  - At gate A's constitutions the rivals win: lowering `ρ` lifts the rivals' growths more than the
    target's.
  - With `E*` the target wins. `E*` makes the target's growth depend on the near data, so the near
    data that a lower transport emphasizes favour the target.

## 3. What this locates [measured; agent-inferred where marked]

**The blocker, by its measurement.** The native comparison's slope in the transport modulus asks for
the lower transport only where `E` already reads the rule (`refit-founded`, `chord-1/2`, `refit`).
Wherever gate A's moves stood, it asked for the higher one (`γ_ρ` from `[−758991, …)/4096` to
`[−332395, …)/4096`). Even where it points down, the chord is between 56 and 287 of its least-squares unit moves.

[agent-inferred] **Neither factor pays alone, as in c2's request 7, but at the scale of the whole
key.**
- With the founded `ρ₀`, even the refit's `E` reads 22 stations right: the far end locks first.
  `E`'s descent at `ρ₀` therefore has no reason to head for `E*`. Gate A found the class preference
  instead, at `L` no lower than `[342226/4096, …)`.
- With gate A's `E`, the comparison asks for the higher `ρ`.
- Only the joint chord descends strictly to the working constitution.
- The modulus is the passage's reach, a part of the source navigator's key. A first-order move from
  the founded opening does not locate it, because its slope sign depends on whether `E` already
  reads the key.

**Endpoint data the next loop starts from.** At `ρ₀`, `E*` alone gives `L` in
`[310210/4096, …)`: below every constitution gate A's moves reached, and with the comparison's slope
in `ρ` pointing down there. A two-leg route exists in its endpoints: `E` first at `ρ₀`, then `ρ`.
Whether each leg descends monotonically is not read here.

## 4. Time and memory

| Read | Measured | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| 7 constitutions at 19 threads | 460,369 ms (launcher), 459,844 ms (harness) | 582,897 ms / `timeout 583` | 151,707,648 |

- **Per constitution**: 42,164, 69,697, 72,336, 67,496, 68,908, 66,778 and 72,425 ms. Each is below
  the per-unit bound of 83,271 ms, so no early stop fired. Measured against projected:
  `460369/582897`.
- **Identities** (`identities.txt`): source `6800536d`; binary sha256
  `6458807bc93f0a1112d75d08b799694600115d3b4ce4c8385328e86d3639a09b`.

Gates: `cargo check --workspace --all-targets` is clean at `6800536d`. The one library change adds a
receipt field computed from the move's existing pairings. No law changed and no Lean changed, so the
library tests and the Lean build were not run.

The receipts (`2026-10-01_THE_MODULUS_SLOPE_receipts/`, synthetic terrain only) are `listing.txt`,
`stderr.txt` (the partial-remount labels) and `identities.txt`.
