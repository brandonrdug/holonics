# The native move at `E` alone: its fixed points and one step's reach

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [proved-derived;
formal-checked] for §1 and §2 (`HNN/ExecutedComparison` §9, `Holon/Element.KineticFace`);
[measured] numbers in §3 are cited from their records; [agent-inferred] where marked. No run.

The main line is ablating the exterior refit's optimizer (`adam`, `rms`, momentum, `sgd`) to name the
ingredient that took `E` from the opening to the refit's representation. This record states what the
native move at `E` alone reaches today, so that whichever ingredient returns is compared against a
stated baseline.

## 1. Fixed points: every candidate rests where the comparison does

Every move in question is a metric's step `−P ∇_E L` with `P` positive definite at each state:
- the normal law's deposition `−M⁻¹Aᵀc`, with `M = I ⊗ H′` the port's retained Gram and `Aᵀc = ∇_E L`;
- the witness's span direction, and every iterate of the kinetic solve, `M⁻¹Aᵀμ_k`;
- an exterior `sgd` step (`P = ηI`), and `rms` and `adam` steps (`P` diagonal and positive);
- momentum at rest (zero velocity).

`metric_step_zero_iff`: `P g = 0` exactly when `g = 0`. The kinetic solve's least-energy minimizer of
`cᵀAv + ½vᵀAᵀFAv` is `0` exactly when `Aᵀc = 0`. **So no metric, step size, schedule or momentum
changes where a move can rest on `L` alone: the stationary points of `L` in `E`.** An ingredient can
only change the path.

The guarded native chain has not stopped at such a point. The kinetic chain's eighth move was refused
by the guards with its solve converged: from move 5 on the larger trials lowered the fixed mask but
raised the machine's own release (`OwnNotBelow`)
([kinetic move](2026-10-02_THE_KINETIC_MOVE_FROM_THE_OPENING_MEASURED_THE_COMPARISON_FALLS_FASTEST_AND_THE_DECISIONS_STAY.md) §1).
Its terminal state is set by the guard, not by `L`.

## 2. One step's reach: the metric's class decides it

From one state with covector `g = ∇_E L ≠ 0`:
- **A full metric reaches every descent direction** (`posDef_reach`): every `d` with `⟨d, g⟩ < 0` is
  `−P g` for a positive definite `P`.
- **A per-coordinate scale reaches exactly the sign-consistent directions** (`diagonal_reach_iff`):
  `d = −diag(p) g` with `p > 0` iff `d_i = 0` where `g_i = 0` and `d_i g_i < 0` elsewhere. `adam`'s first
  step is `−η sign g`.
- **The native family reaches exactly the readings' horizontal space** (`native_step_horizontal`):
  a step `M⁻¹Aᵀμ` is the least-energy lift of its own reading change and has no hidden part. Any
  target `δ` splits `M`-orthogonally into `horizontal(Aδ)` and `hidden(δ)`, with its energy split
  between them (`KineticFace.energy_split`). The native step reaches the first. **No native step from
  this state moves the second, and no reading sees it at first order.** At the opening that space has
  dimension at most the 320 reading coordinates, against `E`'s 600 entries.

## 3. The baseline at `E` alone, measured

Gate A's batch, the lock face at the decisions, `ρ = ρ₀ = 1645392/2^21`:

| State | `L` (`/4096` nats) | Solved of 64 | Stations right |
|---|---|---|---|
| the opening `E₀` | 500197 | 0 | 15 |
| the kinetic chain's last adopted move (native, guarded) | 337896 | 1 | 13 |
| the chord `E₀ + s(E* − E₀)`, `s = 1/4` | 459530 | 0 | 12 |
| `s = 1/2` | 413154 | 0 | 18 |
| `s = 3/4` | 361399 | 6 | 17 |
| `s = 1`, the refit's `E` | 310210 | 15 | 22 |

The native directions at `E₀` against the chord `δ = E* − E₀`, as squared cosines:
- the port's unit move, `16185495/2^34`;
- the witness's span step, `14180265/2^31`;
- every kinetic iterate, within `[−8768139/2^33, 7932255/2^31]` (signed).

A random direction in 600 entries has expected squared cosine `1/600`.

[agent-inferred] At comparable `L` the native chain holds 1 solved and 13 right where the chord holds 6
to 15 solved and 17 to 22 right. `L` does not fix the decisions: the states a path visits do.

## 4. The reads that place an ingredient against this baseline

These are three exact reads at `E₀`, for the main line on its own constitutions:
1. **The chord's energy split.** `½⟨M h, h⟩` against `½⟨M δ, δ⟩`, where `h = hidden(δ)`: the share of
   the chord that no native step from the opening can take.
2. **The chord's sign agreement with `−g`.** The number of the 600 entries where `δ_i g_i < 0`, and
   where `g_i = 0` but `δ_i ≠ 0`: the chord's distance from a per-coordinate step's reach.
3. **The chord's first-order slope** `⟨δ, g⟩`: whether the chord is a descent direction at all.

[agent-inferred] How each ingredient would read against them:
- **Per-coordinate scale** (`rms`, `adam` without momentum) names a metric. It matters where read 2
  is high and read 1's hidden share is large: its step leaves the horizontal space that every native
  step stays in. Its native counterpart is a positive definite change of `M`, certified by the
  factored Fisher form (`HNN/Ratio/Certificate` §7), whose bound holds for any step `D`.
- **Momentum** steps along a sum of past covectors `∇L(E_i)`, each a reading covector at its own
  state. Against the native span the question is read 1 along the path.
- **Step size or schedule** keeps its base's directions and changes the states the path visits. If
  `sgd` with the refit's schedule reaches the refit's region, the ingredient is the path's size or
  the absence of the release guard that stopped the native chain (§1). Its native counterpart is
  then a change to the ladder or the guard, not a new metric.
