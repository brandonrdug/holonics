# The deposit holds the carried momentum, and the accreted mass is the throw's damping

**Date.** October 3. **Issues.** #73, #63, #62, #240. **Grade.** [proved-derived; formal-checked]
for the accretion laws (`HolonicsResearch/HNN/MoveDirection` §9, ported from #240, and §10, new);
[agent-inferred] where marked; [definition; proposed] for the changes to owners this record does not
edit (§5). No run, no control arm, no held-out read.

**Occasion.** Brandon's throw lens (October 2: "Predictive release, it's a throw like of
momentum"), joined to the machine by derivation as the reception carry's interior motion at the
deposit. #240 derived the throw for the constitution's own motion and built an executed arm; the
[reception carry](2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md)
(record B, built on #280 as `Reception::Carry`) carries the field's motion from one reception to
the next. This record states the one law both obey at a deposit.

## Answer

1. **Two motions, one law at the deposit.** The field's motion (record B's carried interior change)
   has the contacts' storage `C_a` for its mass. The constitution's motion (U6's moves of `E`,
   #240) has the source port's Gram `H` for its mass. At a deposit each mass changes suddenly, and
   each motion holds its momentum. In throw terms record B's `A = 0` is the field's throw and
   `A = I` (rest, today's reception) is its leap: the momentum spent at every reception. #240 is
   the constitution's throw. They compose, as record B §3 says, and neither replaces the other.
2. **The contact's canonical state is `(u, π = C_a w)`.** The transit is the midpoint advance on
   `(u, p = C_a w)` with storage `(K_a, C_a⁻¹)` (`propagation.rs`, module docs; the test
   `a_stored_transit_is_the_reference_holons_midpoint_advance`). The solve reads `w` only through
   `C_a w`: its right side is `h(α_g − α_h) + 2C_a w − hK_a u` (`transit_solve`), and the power
   form reads `½⟨w, C_a w⟩`. So the future-sufficient state is `(u, π)`; `w` modulo `ker C_a` is
   read by no later tick.
3. **A deposit holds `(u, π)`.** A deposit is a sudden change of the constitution between two
   ticks. Along the motion `π̇ = −∂P/∂u` and `u̇ = ∂P/∂π` stay bounded across a jump of `C` or
   `K`, so both are continuous: the deposit holds position and momentum and changes the mass.
   The carried rate after it solves `C′_a w′ = C_a w` [proved-derived for the energy below;
   the continuity is the standard sudden-change law of a Hamiltonian, agent-inferred as the
   discrete scheme's law until its Lean statement lands, #62 item 1].
4. **What the deposit does to the carried motion.** With `C′ = C + F` the kinetic reading falls by
   exactly
   ```text
   ½⟨w, C w⟩ − ½⟨w′, C′ w′⟩ = ½⟨w′, F w′⟩ + ½⟨w − w′, C (w − w′)⟩        (held_momentum_loss)
   ```
   the accreted mass's energy at the new rate plus the rate jump's energy in the old mass, for any
   symmetric `F`. For `C, F ⪰ 0` it never rises (`held_momentum_dissipates`), which is
   `(H + F)⁻¹ ⪯ H⁻¹` in the Loewner order (`accretion_inverse_antitone`, #240's owed matrix
   form). The scalar case is #240's sticking loss `p²f/(2m(m + f))` (`accretion_loss`). The
   stiffness part is `½⟨u, ΔK u⟩` under either hold, since `u` is held.
5. **Holding the rate instead injects work no source supplies.** #280's carry, and the
   within-refinement continuation (`word/continuation.rs`: "Contact factors change C, K and D in
   the same (u,w) coordinates"), hold `w`. Across an accretion that raises the reading by
   `½⟨w, F w⟩` (`velocity_held_injects`): the held momentum plus an impulse `F w` with no source.
   [agent-inferred, not read] This is a candidate for the receptions where the main line's fixture
   is not passive (5 of 8 passive); the per-reception terms decide it, and they are the main
   line's read. [measured-exact; the main line's read, record B §2.3 at
   [`58e4707e`](https://github.com/brandonrdug/holonics/blob/58e4707e/research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md),
   #280] The 5 of 8 was a slip in the loss, which omitted the element's passive term. With the
   whole loss the chain is dissipative at all eight receptions, and only the stronger reading
   (the work between words within the next word's loss) fails, at reception 7 alone. Keeping the
   momentum on that fixture moves the failure to receptions 5 and 8, so it does not explain it.
6. **Where the mass shrinks, the deposit does work, and the certificate is the other side.** At a
   held momentum a shrinking mass raises the reading, as a skater pulling in the arms: the work is
   the deposit's, entered in record B's chained balance as `deposition_k`. A mass certified from
   below, `C′ ⪰ C/(1 + ε)` with `1 + ε > 0`, bounds the held momentum's reading by `(1 + ε)`
   (`held_momentum_bound`). The committed storage certificate `Q_(k+1) ⪯ (1 + ε_k) Q_k`
   (`Holon/Deposition.committed_energy_bound`, enforced at the commit) is the bound for the
   stiffness and for a held rate; the held momentum needs the mass bounded from below. Both are
   inertia reads of the same exact forms.
7. **The mass and the damping, read natively.** No constant is chosen at either level.
   - The field: the mass is `C_a`. The damping is the contact's own `hω*D_aω` and its
     conductance on the hop clock, which the transit already dissipates, plus the sticking loss of
     item 4 at each deposit on the deposit clock.
   - The constitution: the mass is `H`, and each deposit accretes the returns' `F = Σ w f fᵀ`. The
     damping is the accretion rate `F/H_k` on the deposit clock, vanishing like `1/k` when the same
     requests return (`throw_velocity_rises`, `throw_velocity_le_terminal`, `leap_velocity_le`;
     #240 §3). A throw from rest reaches no further than free fall (`throw_reach_le_free_fall`).
   - The brief's reading, that `H` with its accreted `F` is the carry's interior mass, conflates the
     two levels: `H` is the mass of `E`'s motion, not of the field's. `E` is not in the power form
     and reaches the contact only as motion
     ([receiving reach](2026-10-02_THE_RECEIVING_MAP_OPENS_AT_ZERO_AND_THE_SOURCE_MAP_REACHES_THE_CONTACT_ONLY_AS_MOTION.md)),
     so the constitution's throw enters reception only through the moment's imposed storage
     `s_(k+1)(0)`, opened with the thrown `E`. Record B already enters that as the source exchange,
     on the source rings, and its `Π_int` holds the interior coordinates. The two throws act on
     complementary coordinates and nothing is counted twice. [agent-inferred] `H` is the storage's
     inertia read through the received moments (the direction record §5); the exact identity of
     `½⟨ΔE H, ΔE⟩` with the imposed storage power is owed (#62 item 3).
8. **#240 can close without its executed Throw arm.** Its laws are kept: §9's accretion Lean is on
   main with this record, together with §10's matrix form, which closes #240 §5's owed matrix
   statement. Its supersession of the [direction record](2026-10-02_THE_COMPARISON_IS_INVARIANT_UNDER_THE_RINGS_SHIFTS_AND_A_GLOBAL_PHASE_AND_THE_GAUSS_NEWTON_STEP_POINTS_TOWARD_A_LOWER_POINT_EXACTLY_WHEN_ITS_CHORD_DESCENDS.md)'s
   agent-inferred flight and damping (§8(b):
   the excursion's interval as the flight, `β = 1 − 2hω_min`) is restated here: the damping is the
   accretion, and the flight is measured, never chosen. The executed arm (`MoveMetric::Throw`,
   `Flight`, `source_coast`, `Constitution::stepped_source_coasting`, `PreparedStep::stepped_coasting`)
   stays in history at [`4743e836`](https://github.com/brandonrdug/holonics/tree/4743e836), to be
   ported when U6's moves resume, under §5's consumer. Its §6 chain (a seed and a control arm) and
   its §8 Kinetic coupling read served only the synthetic step 1 and are dropped. What it still
   owes goes to #62 (items 4 and 5).

## 0. The failures this could repeat

From [the failures that repeated](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
[the prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md), the
[catered-machinery antipattern](2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md),
[the workflow record](2026-09-27_THE_WORK_READ_FROM_ITS_CONVERSATIONS_AND_HISTORY_CONVERGES_WHERE_ACCEPTANCE_IS_FIXED_BEFORE_THE_CLAIM.md)
and [the waiting audit](2026-09-30_AUDIT_WAITING_DEADLINES_AND_CONCURRENCY_THE_WORKERS_BLOCKED_ON_THEIR_OWN_RUNS.md):

- **An authored routine standing in for learning.** Nothing here is a schedule: the hold is the
  transit's own canonical state, the mass is the constitution's own form, and the damping is its
  accretion and its own dissipation. No momentum coefficient enters.
- **A located cause carried unrepaired into a new consumer.** Record B §2.3's balance and the
  fixture's non-passive receptions are the main line's to correct. This record names the hold
  that sets `deposition_k` for contacts and proposes it (§5); it does not build on the uncorrected
  balance.
- **An uncertified deposition step.** The deposit's work on the carried motion is an exact
  identity (item 4), and its bound under shrinking mass is a certificate (item 6), not a hope.
- **A tape as retention.** The carried state is `(u, π)`, the field's present motion, overwritten
  at every reception: not a record of earlier windows.
- **Seen as unseen; bits as progress; a refusal answered with a larger limit.** No run, no score
  and no held-out read. A momentum that a singular `C′` cannot hold is refused, never absorbed by a
  wider bound (§5).
- **Text as the exception; a design in arrays.** The law is stated on the contact's storage and
  the port's Gram, the same for any boundary chart.

The computational object is the helical pair interaction: the contact as the pair's
mass–spring–damper, `C_a`, `K_a`, `D_a` on `(u, w)`. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches the pair
(the contact's state across a deposit), the tube (the reception chain's clocked span) and the helix
(the carried motion's continuation); faces and placement, cell holonomy and the tower thread are
kept attached and unchanged.

## 1. The two holds, side by side

| | held rate (`w`) | held momentum (`π = C w`) |
|---|---|---|
| state after `C → C′` | `w′ = w` | `C′ w′ = C w` |
| kinetic change, `C′ = C + F` | `+½⟨w, F w⟩` | `−½⟨w′, F w′⟩ − ½⟨w − w′, C(w − w′)⟩` |
| accretion `F ⪰ 0` | raises | never raises |
| shrink | lowers | raises; bounded by `C′ ⪰ C/(1 + ε)` |
| from rest, `w = 0` | `0` | `0` (the same state) |
| `F = 0` | unchanged | unchanged (the same state) |
| what the transit reads next | `C′ w` | `C w`, the held momentum |

The last row is the reason: the next tick's solve reads `2C′_a w′`. Under the held rate it reads
`2C′_a w = 2C_a w + 2F w`, a momentum the field never had.

## 2. The proofs

`HolonicsResearch/HNN/MoveDirection` §10, inverse-free on `Matrix n n ℝ`:

- `held_momentum_loss` (`Cᵀ = C`, `C w = (C + F) w′`): the identity of item 4.
- `held_momentum_dissipates` (`C, F ⪰ 0`): the reading never rises.
- `accretion_inverse_antitone` (`H ≻ 0`, `F ⪰ 0`): `(H⁻¹ − (H + F)⁻¹) ⪰ 0`.
- `velocity_held_injects`: `⟨w, (C + F) w⟩ = ⟨w, C w⟩ + ⟨w, F w⟩`.
- `held_momentum_bound` (`C ⪰ 0`, `1 + ε > 0`, `C′ − C/(1 + ε) ⪰ 0`): the held reading is at most
  `(1 + ε)` times the reading before.

§9, from #240 unchanged: `accretion_loss`, `accretion_dissipates`, `thrown_move`,
`throw_velocity_le_terminal`, `throw_velocity_rises`, `leap_velocity_le`,
`throw_velocity_le_unaccreted`, `throw_reach_le_free_fall`, `convex_slope_le`,
`coast_apex_no_floor_ahead`, `coast_floor`, `coast_floor_at_end`, `line_falls_to`,
`coast_secant_curvature`.

## 3. The consumer and its equation

[definition; proposed] The consumer is `Word::open_received` (#280, `word.rs:883`), at
`Absorption::Nothing`: for every contact,

```text
u′_a = u_a,    C′_a w′_a = π_a,    π_a = C_a w_a read at the end of word k
```

with `C_a` the constitution word `k` ran on and `C′_a` the operands at word `k+1`'s cut. Then
`CommitWork::deposition` for the contacts' storage reads `½⟨π_a, w′_a⟩ − ½⟨π_a, w_a⟩`, and
record B's chained balance keeps its form. The constitution's consumer, when U6 resumes, is the
deposit's thrown move `U = ηD + c` through the certified step: `Holon/Deposition.certified_step_descends`
takes any unit step's first-order decrease and curvature, so `U` needs no new certificate, and the
coast is carried only when the power test's first-order decrease along `U` is positive (#240 §4).

## 4. The receipts

Exact checks for the build that consumes this, each an equality or an exact ordering:

1. At `Absorption::Complete` the opening is today's, byte for byte (rest zeroes `w`).
2. From rest, and at `ΔC_a = 0`, the held momentum's opening equals the held rate's.
3. At every reception and every contact,
   `½⟨w, C w⟩ − ½⟨w′, C′ w′⟩ = ½⟨w′, ΔC w′⟩ + ½⟨w − w′, C(w − w′)⟩` exactly.
4. Under accretion that difference is not negative; under a shrink, the held reading is at most
   `(1 + ε)` times the reading before, with `ε` read by inertia.
5. Per reception, the passivity terms of record B §2.3 printed with the held momentum, beside
   their values with the held rate, on the fixture the main line already reads.

## 5. Proposals to owners this record does not edit

Sent to the coordinator for the main line, which owns `word.rs`, `word/continuation.rs`,
`reference.rs` and record B:

1. `ReceptionCarry` carries `[u, π]` per contact (`π = C_a w` with word `k`'s operands), and
   `Word::open_received` solves `C′_a w′ = π` at the new cut. A `π` outside `range C′_a` is
   refused with a typed error naming the contact; its law is owed (#62 item 2). `w′` is fixed only
   modulo `ker C′_a`, which no later tick reads; the solve's own chart fixes it.
2. `ContactCut::continue_deposited` holds the contacts' momentum across its deposit in the same
   way, superseding its agent-inferred "same (u,w) coordinates". [Built, #288: its law at held
   momentum is the
   [storage-resolution record](2026-10-02_A_STORAGE_DEPOSIT_IS_FELT_ONLY_THROUGH_THE_RATE_S_JUMP_AND_THE_WORD_HOLDS_IT_BELOW_ONE_UNIT.md)
   §9.]
3. Record B §2.3 item 1 names the held momentum for the contacts' storage, with `deposition_k` read
   as in §3. The chained balance's form is unchanged.
4. Under the carry the commit reads, beside `Q_(k+1) ⪯ (1 + ε_k) Q_k`, the mass from below,
   `C_(k+1) ⪰ C_k/(1 + ε′_k)`, and reports `ε′_k` per reception as record B's reported excess.
   It is a reading, not a new refusal.

## 6. Owed in #62

1. The discrete scheme's hold: across a jump of the constitution between two midpoint ticks, the
   canonical state `(u, π)` is continuous, and the reception's balance with §10's deposit term.
2. The law of a momentum a singular `C′_a` cannot hold.
3. `½⟨ΔE H, ΔE⟩` as the imposed storage power of the received moments.
4. From #240 §5: the throw's per-move energy law with the certified step's adoption.
5. From #240 §7: the floor along a nonconvex line.
