# The throw carries its momentum through the deposit's accreted mass, and a grip halves it

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the accretion laws (`HolonicsResearch/HNN/MoveDirection` §9);
[agent-inferred] for the choices marked; [definition] for the built arm (`MoveMetric::Throw`). The
chain's run is pinned in §6 and not yet measured. This record supersedes the agent-inferred flight
and damping of the [direction record](2026-10-02_THE_COMPARISON_IS_INVARIANT_UNDER_THE_RINGS_SHIFTS_AND_A_GLOBAL_PHASE_AND_THE_GAUSS_NEWTON_STEP_POINTS_TOWARD_A_LOWER_POINT_EXACTLY_WHEN_ITS_CHORD_DESCENDS.md)
§8(b) (the excursion's interval as the flight; `β = 1 − 2hω_min` from the softest mode). The
deposit law fixes both, so no mode enclosure is needed.

**Occasion.** Brandon: "Too short per fit sounds like 'leap' and tolerance. Predictive release, it's
a throw like of momentum." The main line then measured that the receiver's metric, not the
comparison's shape, turns the Kinetic step from the gradient.

## Answer

1. **The normal law is the leap, read from its own deposit balance.** The source port's deposit is
   `W′H′ = WH + WF + ηG` (Lean `HNN/LatticeWord.deposition_chart_balance`, carry terms aside).
   - The Gram `H` is the port's mass, the storage's inertia (the direction record §5).
   - Each deposit **accretes** the returns' `F = Σ w f fᵀ` onto it: `H′ = H + F`.
   - `G = Σ w g fᵀ` is the impulse the returns deliver.
   - So `W′ = W + ηG H′⁻¹`: the port moves by the impulse through the new mass and keeps nothing
     of its last motion. The momentum is spent at every deposit. That is the leap from rest.
2. **The throw keeps the momentum across the deposit.** The returns stick to the port, so the
   accretion is inelastic and conserves momentum.
   - With velocity `d` (the last adopted move of `E`), the momentum is `P = dH`.
   - After the deposit, `P′ = P + ηG` and the move is `ΔE = P′H′⁻¹ = ηD + c`.
   - `D = G X̂′` is the impulse, the normal law's unit step.
   - `c = dH X̂′` is the **coast**: the last move diluted by the mass the deposit added.
   - From rest (`d = 0`) the throw is the leap (`thrown_move`).
3. **The damping is the accretion; no constant is chosen.**
   - A carried momentum's kinetic reading falls across every deposit by exactly the sticking loss
     `p²f/(2m(m + f))` (`accretion_loss`, `accretion_dissipates`).
   - Under a repeated batch, `H_k = H₀ + kF`. The friction coefficient is then the accretion rate
     `F/H_k`, which vanishes like `1/k` on the deposit clock: a friction with no time constant.
   - Under a constant impulse `i`, the throw's velocity `k i/(m₀ + kf)` rises with every deposit
     toward `i/f` (`throw_velocity_rises`, `throw_velocity_le_terminal`). The leap's `i/(m₀ + kf)`
     falls like `1/k` (`leap_velocity_le`). This is "too short per fit", derived: the leap spends at
     each deposit what the throw carries.
4. **A grip halves the momentum, and the apex releases from rest.**
   - The halving trials halve the whole carried move, `2^(−j)(ηD + c)`. The adopted move is the
     next velocity, so a trial adopted after `j` halvings carries `2^(−j)` of the momentum. The
     conditions of adoption act as grips that absorb it.
   - A refused move leaves the port at rest.
   - Before the trials, the composition's first-order bound along the coast alone is read (the
     power test). The coast is carried only when that bound is negative: the comparison falls along
     the motion. Otherwise the throw is at its apex and the move is released from rest.
   - **The flight** is the run of moves from a release to its apex or to a refusal. It is measured,
     never chosen.
5. **#202's acceptance is unchanged, and `H` is a reading, not a condition.**
   - Every trial of a throw meets every metric's conditions of adoption: the entry bound; the
     first-order certificate on the carried move (coast included); the successor's own
     certificates; the fixed mask strictly lower by disjoint enclosures (the held code length
     falls); and its own released code length within the excursion.
   - So `H = ½⟨P, c⟩ + L_held` need not fall. The held part falls at every adopted move, and the
     kinetic part rises when the force does work along the motion; that is how a throw converts
     descent into carried motion.
   - Requiring only `H` to fall would admit rises of the held code length, which is a pass crossing.
     The main line's read ruled out a pass as the cause (the direction record §8), and that rule
     would bypass #202's held certificate. The kinetic reading `½⟨P, c⟩` is printed on every move.
   - `L` is a code length, not the bank's stored energy (#202 §0). It is the potential of the
     move's own dynamics, and `½⟨P, c⟩` is in the comparison's unit by the normal law's weights.

## 0. The failures this could repeat

From [the failures that repeated](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):

- **An authored routine standing in for learning.** The coast is the port's own normal law: its
  Gram and its chart. No optimizer schedule (Adam, a chosen `β`) enters; Adam stays an outside
  yardstick.
- **A refusal answered with a larger limit (lesson 9).** The throw keeps `LADDER_DEPTH`, the
  lattice floor and the entry scale, read on the whole carried move. No bound is raised.
- **An uncertified deposition step.** Every trial is certified by the same conditions of adoption,
  and the coast is deposited through the same budgeted carry, clock, budget and storage-growth
  certificate as the impulse (`Constitution::stepped_source_coasting`).
- **A tape kept as retention.** The flight is one matrix the size of `E`: the motion's state, not
  a record of past fluxes.
- **Bits read as progress.** The acceptance (§6) reads decisions and held-out sections, not `L`
  alone.

## 1. The question

Does the native move carry velocity? If not, what are the mass, the native damping and the flight
of a throw, and how does #202's acceptance read it?

The native move carries no velocity (the direction record §5). Its mass is the Gram `H`, and its
stiffness is the Fisher pullback. The deposit balance supplies the rest.

## 2. The derivation

**The deposit as accretion.** The source port's normal law carries `(W, H)` and deposits
`H′ = H + F` with `F = Σ w f fᵀ`, then `W′ = W + ηG X̂′`, where `X̂′` is the chart the deposit
refines for `H′` (`NormalLaw::prepare`, `PreparedStep::stepped`). With `B = WH`, the balance
`W′H′ = WH + WF + ηG` reads as an accretion of mass `F` at the port's own position `W` (the moment
`WF`), plus an impulse `ηG`. The port's velocity after the deposit is `ηG X̂′`, set by this deposit's
impulse alone.

**The throw.** A body that accretes mass by sticking conserves its momentum. With momentum `P`
carried into the deposit:
- `P′ = P + ηG`;
- `ΔW = P′ X̂′ = ηG X̂′ + P X̂′ = ηD + c`.

The velocity is carried as the last adopted move `d`, on the port's lattice. Its momentum is read
through the mass at which it was realized, `P = dH` (`Constitution::source_coast`; `H` symmetric, so
each row is `P_r = H d_r`). Each row of the coast is `c_r = X̂′(H d_r)`, the chart applied as the
impulse's chart is (`SolvedChart::reach`).

**What is exact.**
- The velocity `d` lies on the source port's lattice (`2^(−L_s)ℤ`). The carry keeps the deposit's
  sub-lattice remainder, as for every deposit. `d` differs from the exact `ηD + c` only by the
  change of the carried remainder.
- `P`, `c` and `½⟨P, c⟩` are exact rationals.
- The coast is added to the impulse's update before the budgeted carry deposits it, so the
  lattice, the clock, the bit budget and the storage-growth certificate read the whole carried move.

[agent-inferred] **Why the velocity is the realized move rather than the exact update.** It keeps
the flight's size bounded by `E`'s own bits. The exact update's denominators would compound over
the flight. The remainder the lattice holds back is not lost: the carry deposits it later.

**The damping.** For a scalar mode with mass `m`, accretion `f ≥ 0` and momentum `p`:
`p²/(2m) − p²/(2(m + f)) = p²f/(2m(m + f)) ≥ 0` (`accretion_loss`, `accretion_dissipates`).
[agent-inferred] The matrix form, `⟨P, (H + F)⁻¹P⟩ ≤ ⟨P, H⁻¹P⟩` for `F ⪰ 0`, is the antitonicity
of the inverse on positive forms. It is owed in Lean (#62). The chart `X̂′` reads `(H + F)⁻¹` within
its certificate `δ`.

**The rate.** Gate A's chain deposits the same batch at every move, so `H_k = H₀ + kF`. The
continuous form of the throw is `d/dt(H(t)v) = −∇L` with `Ḣ = F`, that is
`H v̇ + F v = −∇L`. The accretion acts as a friction `F` against the mass `H₀ + tF`: per unit mass
it vanishes like `1/t` on the deposit clock. The constant is the deposit's own `F`, not a chosen
time scale. The leap is the limit that spends the momentum at every deposit.

**The apex.** The power the comparison's force delivers along the motion is `−⟨∇L, c⟩`. The
composition's first-order bound along the coast alone encloses `⟨∇L, c⟩`, read on the coast's own
carried successor. A negative upper end certifies that the comparison falls along the coast, and
only then is the coast carried.

[agent-inferred] **Why release at the apex.** Past the apex the coast climbs, and #202's held
certificate refuses a climb. Carrying it would spend the move's trials on halvings that cannot be
adopted. Releasing from rest keeps the move the normal law's.

**The grips.** The trials halve the whole carried move. A trial adopted at `2^(−j)` of the first
carries `2^(−j)` of the momentum, since its move is the next velocity. The halving is the time step:
the coast and the impulse shrink together. [agent-inferred] The impulse's own scaling within the
time step (an impulse is `η` and a coast is `h`, with `η = h²`) is not followed. One halving law
for the whole move keeps one ladder and its work bound.

**The entry scale.** The first trial is held so that no entry of `E` moves by more than the
founding's `½`, now read on the whole carried move. The largest per-unit-step entry is bounded by
the impulse's `u` plus the coast's largest entry over `η₀`.

## 3. What is built

- `hnn::executed::MoveMetric::Throw`: `E` alone, `ρ` held, by the normal law's impulse with the
  flight's coast. `executed_move_in(…, Throw)` releases from rest.
- `hnn::executed::Flight`: the velocity, the last adopted move of `E` or `None`, and the moves since
  the release (a receipt).
- `executed_move_thrown(…, excursion, &flight)` and `ThrowReading`, which carry:
  - the flight met;
  - the coast's momentum, coast and kinetic reading;
  - the power bound and whether the coast was carried;
  - the impulse's first step;
  - the flight after the move: the adopted move with one more move of flight, or rest after a
    refusal.
- `Constitution::source_coast`, `Constitution::stepped_source_coasting` and
  `PreparedStep::stepped_coasting`: the coast through the accreted mass, deposited with the
  impulse.
- `executed move-once … throw` in the harness reads the flight beside its state
  (`<state>.flight`). It writes the next flight beside the adopted state
  (`<out>/<label>-throw.state.flight`).
- `research/records/2026-10-02_THE_THROW_receipts/run.sh`: the 16-move chain of §6.

**Tests.**
- `the_throw_from_rest_is_the_impulse_and_hands_on_its_move`: without a flight, and from an empty
  one, the throw carries no coast, holds `ρ`, adopts one and the same successor, and hands on the
  adopted move as the next velocity.
- `the_thrown_move_carries_its_momentum_through_the_accreted_mass`: from that successor with that
  velocity:
  - the coast's momentum is exactly `dH` at the incumbent's carried Gram;
  - the coast is carried exactly when the power bound is negative (on the fixture it is carried,
    and the first trial, the whole impulse and coast, is adopted);
  - an adopted trial lowers the comparison with `ρ` held;
  - the next velocity is the adopted move.

## 4. What the throw is expected to change

The direction record §8 found the Kinetic step suppressed the well-read directions, and the
Coordinate step following the gradient. The throw's impulse is the Coordinate's `E` part. Its coast
adds the components of successive impulses that keep their sign (a persistent push), while those
that alternate cancel (`carried_velocity`). [agent-inferred] On a chain whose decisions stay because
each move is halved short of them, the throw should be adopted at fewer halvings as its flight
lengthens, and move farther along the persistent part of the gradient per deposit.

## 5. Owed (#62)

- The matrix form of the accretion's dissipation, `(H + F)⁻¹ ⪯ H⁻¹` for `F ⪰ 0`, read through the
  chart's certificate.
- The throw's discrete energy law at the lattice: the bound on `½⟨P′, c′⟩ + L_held` across one
  adopted move.

## 6. The run, pinned before it

**The claim fixed first.** From the opening `c0.state` on gate A's batch (`order2`, seed
`2026093061`, 8 requests) under `lock-dec`:
- the 16-move throw chain ends with `L` below the Coordinate and the Witness chains' at the same
  move count;
- and its held-out whole sections are at least theirs.

Anything less is reported as what it measured: per move, `L`, solved decisions, whole sections and
stations right, the halvings at adoption, the flight's length and whether its coast was carried.

**Commands.**

```sh
cargo build --release -p holonics --example hnn_prediction
# The development read: the release (m0, at rest) and the first coast (m1), each under a loose
# per-move bound that only guards the read.
PROBE_THREADS=<threads> bash research/records/2026-10-02_THE_THROW_receipts/run.sh .local/throw-dev <guard ms> <guard s> 2
# The chain: the per-move bound is the larger of the development read's two moves.
PROBE_THREADS=<threads> bash research/records/2026-10-02_THE_THROW_receipts/run.sh .local/throw <unit ms> <deadline s>
# Held-out: the chain's last adopted state beside the other chains' states at move 16.
cargo run --release -p holonics --example hnn_prediction -- executed evaluate order2 <held-out seed> 128 <out> \
  throw16=<the chain's last adopted state> …
```

The chain's last adopted state is the last `m<k>/m<k>-throw.state` the script printed. A refusal in
flight is followed by a move from the same state at rest, so a refusal costs a move of the 16.

**The projection.** The per-move bound is the largest measured move of the development read. The
throw adds one preparation and one first-order read to the Coordinate move's work, and the same
trials. The chain's deadline is 16 times that bound.

**Early stop.** A move past its per-move bound stops the chain (`read_probe.sh`'s per-unit
watch), which is then reported incomplete. No bound is raised after launch.

**Threads.** `PROBE_THREADS` declares the probe's thread budget (19 by default, the PC's). On the
cloud host with 4 cores it is 4, and the per-move bound comes from the same host's development read.

## 7. Verification

- `cargo check -p holonics --all-targets`: clean.
- The two tests above and `the_kinetic_move_deposits_the_solve_and_keeps_every_guard`, in release:
  see the PR.
- `bash tools/lean_check.sh HolonicsResearch.HNN.MoveDirection`: "Build completed successfully
  (8706 jobs)".
