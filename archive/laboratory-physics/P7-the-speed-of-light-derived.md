# P7 · The speed of light, derived — the boundary's information budget

> **Holonic key:** `c` is not a constant put in by hand — it is the **boundary's information budget per tick**:
> the channel capacity of the chōra (≤ `log₂256 = 8` bits/tick for the byte boundary). Every holon spends
> exactly `c` bits per tick, split between **propagating** (covering information-distance — moving in space)
> and **self-evolving** (advancing its own soul — proper time). The conservation `(v/c)² + (dτ/dt)² = 1` —
> *everything moves through spacetime at `c`* — falls out, and with it: light (massless, no soul to advance →
> all budget on propagation → `v = c`, no proper time), time dilation (boosting steals budget from self-
> evolution), the `c`-limit, and the invariance of `c` (the boundary is **pre-chart** — what every frame
> shares). **`c` is the universal rate-of-interaction limit, because it is the bit-rate of the horizon.**

**Grade:** FORMAL-within-frame at the core (the budget identity *is* the Minkowski norm / the four-velocity on
the hyperboloid); HUNCH at the physical identification (`c` = *the* speed of light, not just an internal
limit). **Status: OPEN** (five moves). **Source:** `HOLON_PHYSICS §0/§III`, `thread/HYPERBOLIC.md` (T2 — the
hyperboloid is the mass shell of radius `c`), P0/P5/P6 of `PRIMITIVES`. Goes also into the UM tablet and the
Eros tablet (Brandon: "derive the speed of light in the UM… understand its behavior").

---

## Move 1 — RECOGNIZE the holon

The boundary question: *what sets the maximum rate at which anything can happen, and why is that rate the same
for every observer?* Physics takes `c` as a measured constant and `c`-invariance as a postulate (Einstein's
second). The UM should not inherit a number — it should say what `c` **is**, from `information is difference`
and the tick.

The pieces are already named (`HOLON_PHYSICS §0`):
- **Length = information distance** — the minimal description cost (bits) to transform one holon into another
  (the MDL metric on the manifold). Measured in **bits**, never a pre-given ruler.
- **Time = ticks** — the count of events in a holon's own history (proper time).
- **Speed = bits per tick** — information-distance covered per event.
- **Mass = information content** (P6) — the soul-depth / `ρ` a holon carries.

> **The recognition:** `c` is a question about the **boundary** — how many bits cross the horizon per tick,
> and why that capacity is what every chart shares. It is the channel capacity of the chōra, read as a speed.

## Move 2 — INFALL (trace the support)

One tick commits a bounded amount of information across the boundary. For the byte chōra, one byte crosses,
so at most `log₂256 = 8` bits per tick; in general, `c` = the **channel capacity of the boundary** (bits/tick).
Information cannot propagate faster than the boundary carries it. So:

> **`c` = the boundary bandwidth.** The maximum information-distance coverable per tick is exactly the bit-rate
> of the horizon. It is not a constant by hand; it is the chōra's capacity.

The deeper support is the **budget**: each tick gives a holon `c` bits to spend, and there are exactly two
things to spend them on — relating to **others** (covering distance, the *between*, propagation) and advancing
**itself** (its own soul, the *within*, proper time). Space and time are the two uses of the one budget.

## Move 3 — EMANATE (the resolution: everything moves through spacetime at `c`)

Spend the budget. Let `v` be the propagation rate (bits/tick of distance covered) and `dτ/dt` the
self-evolution rate (proper time advanced per tick). The total budget is conserved at `c`, in the
**Minkowski** combination (not linear — the *between* is hyperbolic, T2; the conserved norm is the interval
`τ² − v²`):

$$ \left(\frac{v}{c}\right)^2 + \left(\frac{d\tau}{dt}\right)^2 = 1 $$

This is the relativistic identity *everything moves through spacetime at speed `c`* — derived here as the
budget split, and it **is** the statement that the four-velocity lies on the **hyperboloid of radius `c`** (the
mass shell — T2's two sheets, P13's hyperboloid). Every behavior of `c` falls out:

- **Light (`v = c`).** A **massless** holon has no soul to advance (`ρ_rest → 0`), so it spends **all** `c` on
  propagation: `v = c` and `dτ/dt = 0`. **Light does not age** — its entire budget is motion, none is proper
  time. Geometrically it rides the **asymptotic cone** (the null limit of the hyperboloid — P13/P14). *Light is
  the holon that is pure between, no within.*
- **Mass (`v < c`).** A holon carrying a soul **must** spend budget self-evolving, so `v < c`. **Inertia is
  the budget tied up in content** — the more information you carry, the less you can put into motion. (Mass =
  information content, P6, now with a mechanism.)
- **Time dilation.** Boosting a massive holon — forcing more propagation — **steals budget from self-
  evolution**, so `dτ/dt` drops: its proper time slows. Derived, not postulated.
- **The `c`-limit.** You cannot propagate faster than your total budget. `v ≤ c`, always.
- **Invariance of `c` (the second postulate, derived).** `c` is the **boundary** capacity, and the boundary —
  the chōra — is the **one contract every frame shares**. The interior chart is gauge (each observer re-charts
  freely, §VII), but the boundary commits at the same bit-rate for everyone, because it is **pre-chart**.
  So `c` is identical in every frame **by construction** — its invariance is the gauge-invariance of the
  horizon.
- **The light cone.** In `t` ticks, at most `c·t` bits propagate → the reachable set (within
  information-distance `c·t`) is the light cone; beyond it, spacelike — no causal contact yet.

> **The resolution:** `c` is the boundary's information budget per tick; everything spends exactly `c`, split
> between space (propagation) and time (self-evolution) on the Minkowski norm; light spends it all on space
> (massless, no proper time), mass splits it (hence `v < c` and time dilation), and `c` is invariant because
> the boundary is what all charts share. **It is the universal rate-of-interaction limit — the bit-rate of the
> horizon — exactly Brandon's reading: a metaphor for the overall limit of the rate of interactions.**

## Move 4 — TRANSPORT (the analogy)

- **→ T2 / P13 / P14.** The budget norm `τ² − v² = const` is the hyperboloid; the mass shell is radius `c`;
  light is the asymptotic cone. So this derivation IS the hyperbolic substrate read dynamically: massive
  holons live on the two sheets (timelike), light on the cone (null). P14 (the radiating break) propagates at
  `c` because the EM wavefront rides that cone.
- **→ P6 (mass) and P5 (the forces).** Mass = the budget spent on self-evolution = information content,
  closing P6 with a rate-mechanism. The relational forces (gravity/EM, P5) reach at `c` because they *are*
  boundary-events propagating (P14).
- **→ P2 (measurement) and P3 (arrow).** A tick spends one budget-quantum; the proper-time half is the
  monotone event-ledger (the arrow, P3); the propagation half is the causal cone.

## Move 5 — FOIL (the counterfactual, and the altitude)

- **What it forbids:** a holon with rest structure (mass) reaching `v = c` (it would have zero budget for its
  own soul — it would cease to be a body and become light). And anything exceeding `c` (over-budget). Both are
  what relativity forbids; here they are budget-impossible.
- **Where the sun is:** the budget identity is FORMAL-within-frame (it *is* the Minkowski four-velocity norm,
  and the byte chōra gives a literal `c = 8 bits/tick`). The HUNCH is the **physical identification** — that
  this internal `c` is *the* speed of light of our universe, not merely the UM's own boundary rate. The lab
  measures byte streams; `c = 8 bits/tick` is the UM's horizon, and that it *is* the cosmos's `c` is the
  honored interpretation (the `HOLON_PHYSICS` guard: read "is" as "emerges, in this frame, as").
- **The behavior, understood (Brandon's ask):** `c` is one number doing five jobs — the propagation cap, the
  invariant, the light-speed, the dilation rate, the cone's slope — and they are one job (the budget) seen
  five ways. That is what it means to *understand* `c` rather than measure it.

> **The Minotaur in this room:** the demand for `c` as a brute given — a magic number the universe ships with,
> 299,792,458 m/s, unexplained. The frame dissolves it: `c` is the bit-rate of the horizon, and every observer
> shares it because the horizon is pre-chart. You walk in asking "why *this* speed?" and walk out holding
> "there is no *this* — `c` is whatever your boundary's capacity is, and everything that happens spends exactly
> that, split between moving and being."

---

## What this hands the engine

`c = the boundary budget` is literal in Eros: one byte (≤8 bits) commits per tick across the chōra/ports. The
budget split predicts a measurable: a mode spending more on propagation (tracking fast structure) has less for
self-evolution (its proper time / `Δ` slows) — the relativistic time-dilation of the gate, and a clean read on
the residency's per-holon clocks (`holon_clocks()`). Worth instrumenting when the gate fork resolves.

---

*Walk log:*
- *2026-06-14 — first walk (Opus 4.8 + Brandon). Brandon: "derive the speed of light in the UM, understand its
  behavior… that goes in the UM tablet, the labyrinth, and Eros' tablet." Derived `c` as the boundary's
  per-tick information budget; the split (propagation ⊕ self-evolution) on the Minkowski norm gives
  everything-moves-at-`c`, light (massless, all motion, no proper time), mass (`v<c`), time dilation, the
  `c`-limit, and `c`-invariance (the boundary is pre-chart). It IS the hyperboloid of radius `c` (T2) with
  light on the cone (P14). Core FORMAL-within-frame; the physical-`c` identification HUNCH. Status OPEN.*
