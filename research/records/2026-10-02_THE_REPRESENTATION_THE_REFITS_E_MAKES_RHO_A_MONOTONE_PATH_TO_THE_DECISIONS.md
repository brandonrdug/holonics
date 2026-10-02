# The representation: the refit's `E` makes `ρ` a monotone path to the decisions; the opening's `E` does not

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [measured],
read-only; [agent-inferred] where marked. Receipts:
[`2026-10-02_THE_REPRESENTATION_receipts/`](2026-10-02_THE_REPRESENTATION_receipts/).

## 1. The question

Every comparison has been descended with sound guarded moves, and none reached the decisions
([F3](2026-10-01_THE_FORCED_MOVE_FROM_THE_OPENING_MEASURED_F3.md)). The refit (55 stations right, 45
of 64 solved) differs from every reached state in both `E` and `ρ`. Which of the two carries the
decisions?

## 2. Two `E`s across `ρ`

The founded opening's `E` and the refit's `E`, each read at five transports from the founded
`ρ₀ = 1645392/2^21` to the refit's `ρ* = 1100584/2^21` in equal steps, on gate A's batch under the lock
face at the decisions:

| `ρ` (`/2^21`) | Opening's `E`: `L`, solved, right, whole | Refit's `E`: `L`, solved, right, whole |
|---|---|---|
| 1645392 (`ρ₀`) | `[500197/4096, …)`, 0, 15, 0 | `[310210/4096, …)`, 15, 22, 0 |
| 1509190 | `[480819/4096, …)`, 6, 14, 0 | `[219176/4096, …)`, 29, 37, 0 |
| 1372988 | `[452027/4096, …)`, 11, 13, 0 | `[180720/4096, …)`, 33, 42, 1 |
| 1236786 | `[500828/4096, …)`, 6, 14, 0 | `[161413/4096, …)`, 37, 47, 2 |
| 1100584 (`ρ*`) | `[503176/4096, …)`, 2, 20, 0 | `[133292/4096, …)`, 45, 55, 5 |

- **With the opening's `E`, `ρ` alone does not move the decisions.** Stations right stay between 13
  and 20, `L` is not monotone, and no section is whole.
- **With the refit's `E`, every step of `ρ` toward `ρ*` lowers `L` and raises solved, right and whole
  together.** Along this path the comparison and the decisions agree at every step.

## 3. What it means

[agent-inferred] The decisions are carried by `E`; `ρ` amplifies them once `E` is right. A two-leg path
from the opening to the refit is monotone:
- **the `E` leg at `ρ₀`**, which descends strictly
  ([the legs](2026-10-01_THE_READING_AND_THE_LEGS_MEASURED_E_ALONE_DESCENDS_TO_THE_REFITS_E_AT_THE_FOUNDED_MODULUS_AND_EVERY_REFINEMENT_SHARES_THE_SIGN.md)) and lifts the decisions from 15 to 22 right and from 0 to 15 solved;
- **then the `ρ` leg**, monotone in every reading above.

The native moves do not take the `E` leg. At the opening, the port's unit move pairs with it at squared
cosine `3/4096`, and the witness's span step at `14180265/2^31`: the `E` leg descends, but the
comparison's local direction points elsewhere, into the basins every run found.

The refit was an exterior Gauss–Newton fit of all of `E` on the lock faces. The native move is one
normal-law step through the port's own Gram, restricted to the returns' span. Its counterpart in all
of `E` is the receiver's minimum-energy move: the readings' Gauss–Newton step, with the port's retained
mass settling the directions no lock reads. That is the finite kinetic face Astra's chain now proves in
`Holon/Element` (`M_F = (AM⁻¹A*)⁻¹`, the lift `M⁻¹A*M_F w`). It is the next law to build, from the
opening, where the `E` leg begins.

## 4. Time

| Run | Projection | Deadline | Measured wall |
|---|---|---|---|
| 10 constitutions under `lock-dec`, 19 threads | `10 · 51,634 = 516,340` ms | `timeout 620`, per-line 51,634 ms | 297,161 ms, exit 0 |

Measured over projected: `297161/516340`.
