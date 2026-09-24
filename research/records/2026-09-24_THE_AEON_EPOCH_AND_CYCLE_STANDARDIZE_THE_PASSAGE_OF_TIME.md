# The Aeon, the Epoch and the Cycle standardize the passage of time

[project-postulate] Brandon, September 24, 2026. **Aeon**, **Epoch** and **Cycle** are the
standard vocabulary for the passage of time. "Session", "episode", and counters named
`epoch`/`cycle`/`generations` that serve as one global clock are retired as terms for time.
The ruling came from auditing the code. "Session" appears about 1,120 times in Rust (66 files),
about 1,300 times in Markdown and 19 times in Lean. `epoch` (555 Rust uses), `cycle` (654) and
`generations` (331) served as separate privileged counters. Every one of them named a window
that the program chose, not a structure of the mathematics.

[definition] What we had made rigorous was spatial continuation: the tube, the tower, the
Holarchy and relative completeness. Coarse graining in time had no object of its own. It lived
implicitly in generator clocks and tubes, and explicitly only in process windows. This record
supplies the temporal object from the existing elementary objects.

## The three terms

[definition] **Aeon.** An arbitrary container of causality in time. It is part of a
Holarchy's parametric orientation: the stretch of the Holarchy's motion between two
occurrences.
- The Holarchy's generators carry clocks with phase lifts. Their joint phase lives on a torus
  `𝕋ᵏ`, and its lift to `ℝᵏ` retains winding (helix = circle + carry).
- An aeon `γ` is a 1-chain of the motion in that lift. It is not an interval of a privileged
  clock. Occurrences (the Lean foundation's events) bound it.
- An aeon is arbitrary: any causal span of the motion is one. Aeons compose by concatenation.

[definition] **Epoch.** A division of an aeon. A receiver's clock ticks when the motion crosses
the receiver's section `Σ_R`; parametron: "a section crossing is a clock tick". The ticks
partition an aeon into epochs at that receiver's grain.
- The partition belongs to the receiver and grain: another receiver or a coarser grain
  partitions the same aeon into different epochs.
- Coarsening merges epochs. Counting returns to a sub-section `Σ′ ⊂ Σ` is the first-return
  (induced) map, and the Odometer's carry is the same operation on a digit clock.

[definition] **Cycle.** A closed loop: completeness, not a measurement of duration. An aeon
that returns to its phase state is a cycle.
- Its readings are whole windings, the homology class paired with a clock class.
- Exact parts integrate to zero around it (Stokes), so its readings are gauge-free and
  invariant under deformation.
- A cycle conserves its frames in time: whatever a receiver reads over a cycle is a conserved
  count, not an elapsed quantity.

## How much time passed: a pairing, not a frame

[definition] A receiver's clock is a closed 1-form `ω_R`: `dθ_R` for a phase clock, or
`−U_μ dx^μ` for an observer with four-velocity `U` on a world tube. Elapsed time for `R` over
an aeon is the holon/coholon pairing:

```text
t_R(γ) = ⟨ω_R | γ⟩ = ∫_γ ω_R = n_R + r_R
n_R ∈ ℤ   whole windings: the quotient, the carry
r_R       open phase: the remainder
```

- **No frame is privileged.** Every receiver pairs the same aeon with its own form. The rate
  between two receivers is the typed ratio of their two readings, "one per two".
- **Composition.** Readings add under concatenation, with the carry cocycle:
  `winding(x+y) = winding x + winding y + carry`.
- **Cycles.** A cycle reads `r_R = 0` for every integral clock, and its `n_R` is topological.

## Coarse graining, flux and winding

[definition] **Flux.** Epoch ticks per unit parameter are the flux of the motion through the
receiver's section, `∫_{Σ_R} ρ v·n dS` for the flow's invariant density. The time a receiver
counts is the flux of the Holarchy's motion through its section. It does not matter whether the
motion is read as a push or a pull: the count is the flux.

[proved-standard; stated hypotheses] **Across grains.** For a measure-preserving return map
that is ergodic on the section, Kac's lemma gives a mean first-return time to `Σ′` of
`μ(Σ)/μ(Σ′)` fine epochs per coarse epoch. How much finer time passes per coarse epoch is
therefore a ratio of section measures, not a property of a privileged clock.

[proved-standard] **Two clocks and their crossing axes.** Take two clocks with frequency ratio `α`.
- If `α = p/q`, the pair locks, and every aeon of `q` ticks is a cycle. `p/q` is the pair's Farey
  lock address (`q·v_a = p·v_b`), where the two section axes on the torus intersect.
- If `α` is irrational, no aeon is a cycle. The natural epoch grains are then the
  continued-fraction convergents `p_n/q_n`, where `|q_n α − p_n| < 1/q_{n+1}`: near-returns at
  every grain, closure at none. The three-distance theorem bounds the gap structure at each
  grain.

The winding therefore decides where the Holarchy's own temporal boundaries fall.

## What it joins

- **Retention.** An aeon's boundary is where the future-sufficient quotient of the constitution
  is taken. What rests at a boundary is the retained constitution, not a record of the aeon's
  interior. A "session save" was a program-chosen proxy for this.
- **The Holarchy.** In space, the Holarchy decomposes the whole per receiver and grain
  (`view`, `count`). Its parametric orientation carries aeons, which decompose in time per
  receiver and grain (epochs). `count` exists only under a certified section, as in space.
  Together they decompose the world tube.
- **Open work this subsumes:**
  - the plan's clock-axis joining (§3.6, `join_axes`): two closed forms over one aeon, which
    commute or return their holonomy;
  - the time/entropy chain crossing (#5): the entropy-production clock as one more closed form;
  - Brandon's several axes of parametric time for cross-entropy: its rate along an aeon depends
    on which clock form parametrizes it.
- **Existing owners:**
  - Lean: `Geometry/PhaseCarry` (lift, carry), `Transport/CellHolonomy` (cycles and holonomy),
    `Objects/Pairing`, `Physics/ObserverBoundaryCurrent` (the observer covector),
    `Transport/ChangingReceiver`;
  - Rust: `holonics::geometry::winding` (`Odometer` as a tower of epochs, `LockAddress`).

## Obligations (Lean first, then Rust)

1. **Additivity:** readings add under concatenation, with carry.
2. **Cycle readings:** a cycle reads whole windings that are invariant under homotopy (exact
   forms vanish on cycles).
3. **Quotient and remainder:** the split into windings and open phase agrees with the ratio's
   division with remainder.
4. **Convergent near-return:** the bound for two clocks, from continued fractions.
5. **Kac relation:** between epoch grains, under measure-preservation and ergodicity.
6. **Epoch partitions:** under a certified section, refinement and coarsening form a tower.

Construction is part of K1 (#72), beside the Holarchy. The HNN's interface is then defined over
aeons:
- open from a retained quotient;
- advance along the generator clocks;
- receive at receivers' sections;
- close at an aeon boundary, with the future-sufficient quotient.

This replaces the retired "session" types. M1 does not rename those types in place: it deletes
the superseded ones and leaves the field interface for K1.
