# The commitment is read on the turn clock: its order has a temperature of one turn, and a crossing enters the first order

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the theorems of `HolonicsResearch/HNN/OrderTemperature` (§2, §4, §5); [derived]
where marked; [agent-inferred] for the one premise of §3 and for the release law of §6. No run: §8
lists what the main line reads. Nothing in Rust changes here.

**Occasion.** Brandon asked why the temperature is fixed. The lock face reads each station's classes
as Gibbs shares at inverse temperature one, the growth over one turn (the Lean thread, today). The
[flip record](https://github.com/brandonrdug/holonics/blob/a7d404ea/research/records/2026-10-02_A_FLIP_IS_SET_BY_THE_LOCK_RULES_MARGIN_AND_NO_LAW_IN_THE_CHAIN_CERTIFIES_IT_BEFORE_THE_SUCCESSOR_IS_READ.md)
(on #207) located `m7`'s jump in the **order** in which stations commit, and closed with: "at a
finite temperature the commitment would be a continuous occupation and the jump a steep but
continuous change. The chain runs no finite-temperature release, and this record proposes none."
This record derives the temperature at which the order is read, from the clock the lock is read on,
and states what that reading does to the native move.

**Answer.**
1. One comparison reads at two temperatures. It reads a station's classes over one turn, and the
   order of the stations' commitments at zero temperature. Every jump the move cannot certify lives
   in the second.
2. A station commits at an instant on the turn clock: the number of turns after which its lock
   face, read over that many turns, places its top within the receiver's grain (§2, derived). That
   instant orders by the log ratio of top to runner, which the flip record had marked as the face's
   own variable but could not derive.
3. The lock is read once per turn, and the clock's origin is gauge. The only reading of the order
   that does not depend on the origin is the partition of the circle of origins into three arcs: `A`
   first, both in one turn, `B` first. Their lengths are `clamp(Δ)`, `max(0, 1 − |Δ|)` and
   `clamp(−Δ)`, with `Δ` the instants' difference in turns (§3). So the order's temperature is one
   turn: the same grain as the classes' inverse temperature one. It is fixed by the clock and is
   not a parameter.
4. Read this way, the comparison has no jump. A crossing costs `Δ′ (C_A − C_C)` per unit step
   while `A` leads by less than a turn, a first-order term the move can read before it crosses
   (§4).
5. Where the move's slope is negative, some halving is adopted. At zero temperature a jump present
   at every small step refuses every halving. That is `m7`'s refusal from `1/16` to `1/2048`.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches **the helix**
(a commitment instant is a winding count plus a phase in the turn: the carry and the circle) and
**faces and placement** (the order in which committed data are placed beside later stations). The
pair, the cell holonomy, the tube and the tower thread stay attached: no contact, restriction or
transport changes.

## 0. The recorded failures this could repeat

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **An uncertified deposition step.** The temperature changes what the comparison reads, not how a
  step is adopted. Every step is still re-read whole and adopted only on a certified decrease (§4).
- **A refusal answered with a larger limit.** Nothing here lengthens a run or loosens a condition.
  The jump is removed by reading the order at the clock's own grain, not by paying for it over more
  steps.
- **A located cause carried unrepaired.** The located cause is that the order is read finer than
  the clock reads it, which is the same kind of defect the certified-lock rule repaired for cell
  ends. Its repair belongs in the order's owner (§6), not in the move.
- **Text run on its codec's grain.** The turn clock, the lock face and the grain are the receiving
  bank's, the same for text, image, acoustic and motor charts.
- **A design thought in the programming language.** The partition is a partition of the clock's
  gauge circle into arcs with exact lengths, not a sampled average.

## 1. One comparison, two temperatures

[derived; the flip record §0, the Lean thread's temperature finding]
- **The classes are read over one turn.** A candidate's reading `a_x` is the bank's growth over one
  turn of the passage with `x` placed. The lock face `ℓ = −log θ_t`, `θ_x = a_x/(1 + Σ_y a_y)`, is
  the target's code length under Gibbs shares at inverse temperature one. Read over `n` turns the
  shares are `a_x^n/(1 + Σ a_y^n)`, inverse temperature `n`.
- **The order is read at zero temperature.** The release commits the stations of the largest gap
  first, all or nothing, and each committed datum enters every later station's storage. The order
  is a function of the readings with jumps where two gaps cross.
- **The jumps are all in the order.** Between crossings the comparison is read on fixed sections
  and is continuous; the first-order certificate covers it. At a crossing it jumps by
  `J = C_A − C_B`, the code length on the two orders' sections at the same constitution. `J` does
  not shrink with the step (the flip record §2, §2b; `flip_defeats_first_order`).

So the comparison already reads the classes at the turn's temperature and reads the order at none.
The rest of this record reads the order at the turn's grain too.

## 2. The commitment instant

[derived; `commitResidual_strictAnti`, `commit_instant_le`, `commitResidual_ge_one`]

Read over `n` turns, a station's top share is `θ_top(n) = a_top^n/(1 + Σ_y a_y^n)`. Its code length
is `−log₂ θ_top(n) = log₂(1 + R(n))` with the **commitment residual**

```text
R(n) = a_top^(−n) + Σ_(y ≠ top) r_y^n,      r_y = a_y / a_top.
```

The first term is the resting state's weight against the top, the others are the rivals'. The
receiver resolves code length to the grain `τ` (the declared `1/16` bit, the root of every scale,
PR #150). So the station **commits at the instant `t` where its top's code length reaches the grain**,
`R(t) = 2^τ − 1`.
- **The instant is unique.** Past the threshold (`a_top > 1`) and with every rival below the top
  (`r_y < 1`), `R` falls strictly with `n`. Its value at `n = 0` is the number of classes,
  above `2^τ − 1 < 1`, so it meets the level exactly once.
- **Below the threshold no station commits.** With `a_top ≤ 1`, `R(n) ≥ 1` at every `n ≥ 0`. This is
  the release's threshold, read as a commitment that never arrives.
- **A station whose residual lies below another's at every instant commits no later.**
- **The two-class instant.** With one rival and a top far above one, `R(n) ≈ r^n` and
  `t = c/ln(a_top/a_run)`, `c = −ln(2^τ − 1)`. At `τ = 1/16`, `c ∈ (3117/1000, 3118/1000)`. So
  stations commit in order of the log ratio `ln(a_top/a_run)`, the largest first. The flip record
  (§0) noted that the face orders by the log ratio while the release orders by the difference
  `a_top − a_runner`, and graded the difference the one term the face does not derive. The instant
  derives the log ratio, with the threshold term beside it: near the threshold, `a_top^(−n)` decays
  slowly and sets the instant.

**What is derived and what is not.** The instant is derived from the lock face and the grain. That
the receiver reads the commitment at its instant, rather than by ranking gaps, is the release law of
§6. It changes HNN behaviour and is not built here.

## 3. The order's temperature: one turn, from the clock's gauge

**The premise.** [agent-inferred] The lock is read once per turn. A commitment is known at the first
whole turn at or after its instant, and nothing finer. The reason: the reading `a_x` is a growth per
turn (a Floquet multiplier of the passage), and no owner reads a commitment inside a turn. The flip
record states the same principle for ticks: "events its resolution cannot order are co-present for
it, as two events closer than one tick have no order on that clock."

**The gauge.** [derived from the premise] The turn boundaries are the instants `φ + k`, `k ∈ ℤ`, with
`φ` the clock's origin. Nothing fixes the origin: there is no privileged clock (CLAUDE.md, the aeon
law: elapsed time is windings plus phase, read by a receiver). Station `A` is read before `B`
exactly when a turn boundary falls between their instants. For `Δ = t_B − t_A`:
- with `0 ≤ Δ < 1`, a boundary falls in `[t_A, t_B)` for the share `Δ` of origins;
- with `Δ ≥ 1`, for every origin.

**The partition.** A reading that does not depend on the origin weighs the origins by a probability
on the circle that every rotation leaves fixed. The uniform measure (the circle's Haar measure) is
the only one. So the gauge-free reading of the order is the partition of the circle of origins into
three arcs (`aheadShare`, `copresentShare`, `shares_sum`, `copresentShare_eq`):

| Arc | Length | The release on that arc |
|---|---|---|
| `A` a turn before `B` | `clamp(Δ) = min(1, max(0, Δ))` | `A` commits, then `B` reads `A`'s datum |
| both in one turn | `max(0, 1 − |Δ|)` | `A` and `B` commit together |
| `B` a turn before `A` | `clamp(−Δ)` | `B` commits, then `A` reads `B`'s datum |

- **A turn apart, the order is read whole** (`aheadShare_of_one_le`): the zero-temperature order.
- **At a tie, both commit together on the whole circle**: the certified-lock rule's co-presence.
- **In between, the arcs move by at most the change in `Δ`** (`aheadShare_lipschitz`). The kernel is
  piecewise linear with width one turn and rate one per turn. It has no tails: beyond a turn the
  share is exactly zero.

**This is why the temperature is fixed.** The classes' inverse temperature one and the order's width
of one turn are the same grain, the turn the lock is read over. Neither is chosen. A finer order
would need a reading inside the turn, and a coarser one would discard turns the clock counts.

[refused alternative] Giving each station its own unread phase, independent of the other's, gives a
smooth kernel (the difference of two uniform phases). Both stations are read on the one receiving
bank's clock, so they share one origin, and that alternative reads a freedom the clock does not
have.

## 4. What the reading does to the comparison

[proved-derived; formal-checked] Along a step `η`, write `C_A`, `C_C`, `C_B` for the comparison on the
three orders' sections, each continuous where its order holds, and `Δ(η)` for the instants'
difference. The comparison read at the turn's grain is

```text
Φ(η) = clamp(Δ) C_A + max(0, 1 − |Δ|) C_C + clamp(−Δ) C_B.
```

- **No jump** (`threeOrder_continuous`, `orderMixture_continuous`). Where `Δ` and the three
  comparisons are continuous, so is `Φ`. A crossing of the instants passes `Φ` from `C_A` through
  `C_C` to `C_B` over two turns of `Δ`.
- **A crossing becomes a first-order term** (`orderMixture_hasDerivAt`). For any kernel `p`, the
  slope of `p(μ) C_A + (1 − p(μ)) C_B` is the two orders' slopes at their shares plus the
  anticipation `p′ μ′ (C_A − C_B)`. For the turn clock with `0 < Δ < 1`, the slope is the held slope
  of the shares' sections plus `Δ′ (C_A − C_C)`. That is **the cost of the crossing per unit step**:
  the rate at which the step moves the instants, times the code length between committing in order
  and committing together.
- **The anticipation pays the jump exactly** (`anticipation_integral`): its integral over a segment
  is the cost times the change in share. Over a whole crossing it is the zero-temperature jump.
- **A negative slope is adopted by some halving** (`eventually_lt_of_neg_slope`,
  `halving_adopts_of_neg_slope`); only the slope from the right is used, so the kernel's corners do
  not matter. **At zero temperature a jump at every small step refuses every halving**
  (`jump_refuses_every_halving`). So under the turn clock's reading the move's step sizes either
  find a decrease or the slope says there is none at this state. A cost that stays fixed as the step
  shrinks no longer exists.
- **The anticipation pushes toward the cheaper order** (`anticipation_pos_iff`). With the share
  rising, the anticipation raises the slope exactly when the step moves the instants toward the
  costlier order. The move's descent direction carries a component away from a costly crossing and
  toward a profitable one, before it reaches either.
- **What the receiver's resolution leaves unread** (`orderMixture_resolution`). With the instants'
  difference known to within `w` turns, the comparison is known to within `w` times the larger of
  `|C_A − C_C|` and `|C_C − C_B|` from the order (rate one). At zero temperature an uncertainty of any size in the margin's sign leaves the
  whole `|J|` unread. Here it leaves `w` of a turn of it.
- **Off the crossing, sharpening returns the zero-temperature comparison**
  (`occupation_sharpens_pos`, `occupation_sharpens_neg`, `orderMixture_sharpens`): any kernel read
  at a growing inverse temperature tends to `C_A` where the margin favours `A` and to `C_B` where it
  favours `B`. The turn clock's kernel already reads the zero-temperature order once the instants
  are a turn apart.

**What it does not do.** It does not bound a crossing before the successor is read: the segment
bound on the readings' motion (the flip record's missing `Λ`) is still absent, and adoption is still
the successor's exact re-read. It removes the part of the cost that did not shrink with the step.
It does not say the move reaches the refit's basin or any held-out decision.

## 5. What it costs to read

[derived]
- **Only pairs within one turn need another release.** The kernel is exactly zero beyond a turn,
  so the comparison at a state needs `C_C` (the pair committed together) for each pair of stations
  whose instants lie within a turn, and `C_B` when `B` is the earlier. A pair further apart costs
  nothing. The release owner already releases with a declared lock order
  (`hnn::prediction::bank_release_forced`, forced locks); a pair forced together is the same law.
- **The anticipation needs the instants' first variation.** `Δ′` is the change in `t_B − t_A`
  along the step, from the candidate covectors through `R`: `t′ = −R_a·a′/R_n`, the readings'
  variation over the residual's fall per turn. The candidate covectors are already read at the
  decision sites; reading them at the pair's refinement is the flip record's "the same law would
  give each gap's slope at `r₀`".
- **Exact arithmetic.** The instants are logarithms of readings, so `Δ` is an enclosure with exact
  endpoints, and the arcs are enclosures with exact rational endpoints (`clamp` of an exact
  endpoint). No float enters.

## 6. The release's order law (proposed; changes behaviour)

[agent-inferred; not built] The consistent release reads the order on the same clock as the
comparison: a station commits at the turn of its instant, and stations whose instants fall in one
turn commit together. At a declared origin this is one release. Over the circle of origins it is the
partition of §3, and the released code length the comparison reads is its expected value over the
arcs. Where two arcs release different classes, generation holds the section plural, as it already
does for an unresolved reading. The current rule, largest gap first, is that law's proxy: it orders
by the difference instead of the log ratio and resolves the order inside the turn, finer than the
clock reads. Changing it changes HNN behaviour and needs campaign 1's held-out read before it merges.

## 7. The memory length and the turn

[agent-inferred] Brandon's question also touched the memory length `ρ`. The founding's ceiling on
`ρ` is a statement about the same clock from the storage's side
([the joined move](2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md) §1):
the phase record identifies a datum's age only within one turn, so a datum one turn old must weigh at
most one chart unit, `ρ^d ≤ 2^(−L_ν)`.
- The storage reads the **phase** within the turn and not the count of turns: a turn-old datum would
  alias onto the present.
- The lock reads the **count** of turns and not the phase within the turn: commitments in one turn
  are co-present.

These are the helix's two parts, the circle and the carry. So the order's temperature and `ρ`'s
ceiling are two faces of one fact, that the turn is the receiving clock's grain. They fix different
quantities: the order's width and `ρ`'s upper bound. Neither fixes `ρ`'s value below the ceiling.
That value moves with the joined move (#220) and its basin is the Lean thread's subject.

## 8. What the main line reads

All at `m7`'s incumbent (the state whose move was refused at every step size from `1/16` to `1/2048`)
on request 3, which carries the flip, with the pair that swaps commitment order:
1. **The pair's instants.** Each station's `a_top` and rivals' readings, the instants `t_A`, `t_B` at
   `τ = 1/16` bit (§2), and `Δ` at the incumbent and at the `1/2048` successor.
   - If `|Δ| ≥ 1` at both, the clock reads the crossing as a true order change a turn wide, and the
     instants cross somewhere along the step.
   - If the instants do not cross along the step (the log ratios keep their order while the gap
     differences swap), `m7`'s jump is an artefact of ordering by the difference, and the release law
     of §6 alone removes it.
2. **The co-present release.** `C_C`: the comparison on request 3 with the pair committed together.
   With `C_A` (the incumbent) and `C_B` (the swapped order, `C_B − C_A = 34038/4096` at the
   successor) this gives the ramp's two costs.
3. **The anticipation at the step.** `Δ′` along the kinetic move's direction, and the predicted slope
   `d_held + Δ′ (C_A − C_C)` where `0 < Δ < 1`.

Read 1 decides whether the turn clock's reading reaches `m7` at all. If it does, reads 2 and 3 give
the slope the move would have read before the crossing, against the `+34038/4096` it paid after.

## 9. Verification

- `lean/HolonicsResearch/HNN/OrderTemperature.lean` imports only Mathlib. It was elaborated with
  `lake env lean` against Mathlib `v4.33.0` (rev `db584cd6`, the repository's pin) with no errors,
  warnings or `sorry`, and built in the repository with
  `bash tools/lean_check.sh HolonicsResearch.HNN.OrderTemperature` (receipt in the PR).
- No Rust changed, so no cargo gate applies.
- Owed (#62): the three-order slope with the turn clock's kernel as one theorem at its corners (the
  right slope exists; the file proves the two-order slope for a differentiable kernel and the
  kernel's continuity and rate); the arcs' lengths as a measure on the circle of origins (derived in
  §3 by the boundary count, not formalised); and the release law of §6, if built.
