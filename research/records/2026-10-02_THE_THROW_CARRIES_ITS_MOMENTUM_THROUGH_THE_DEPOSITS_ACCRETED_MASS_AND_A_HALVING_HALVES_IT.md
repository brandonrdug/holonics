# The throw carries its momentum through the deposit's accreted mass, and a halving halves it

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
   - Along the chain `H_k = H₀ + Σ_(j<k) F_j`, each `F_j` read on its own move's sections, so the
     mass a deposit adds is not constant. With the same requests at every move and `F_j` modelled
     as one `F` (the Lean's constant `f`), `H_k = H₀ + kF`, and the friction coefficient is the
     accretion rate `F/H_k`, which vanishes like `1/k` on the deposit clock: a friction with no time
     constant.
   - Under a constant impulse `i`, the throw's velocity `k i/(m₀ + kf)` rises with every deposit
     toward `i/f` (`throw_velocity_rises`, `throw_velocity_le_terminal`). The leap's `i/(m₀ + kf)`
     falls like `1/k` (`leap_velocity_le`). This is "too short per fit", derived: the leap spends at
     each deposit what the throw carries.
4. **A halving halves the momentum, and the apex releases from rest.**
   - The halving trials halve the whole carried move, `2^(−j)(ηD + c)`. The adopted move is the
     next velocity, so a trial adopted after `j` halvings carries `2^(−j)` of the momentum.
   - A refused move leaves the port at rest.
   - Before the trials, the composition's first-order bound on the first trial's whole move,
     impulse and coast together, is read (the power test): the force's power on the motion. The
     coast is carried only when that bound is negative. Otherwise the throw is at its apex and the
     move is released from rest. (#240 first read the coast alone; §2 says why that was wrong.)
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
  `LADDER_DEPTH`'s 8 is a chosen work bound (#230); whether the receiver's resolution derives it
  waits on #236, and this sentence holds whichever way that settles.
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

**The rate.** Gate A's chain deposits the same requests at every move. Their `F_j` is read on each
move's own sections, so it varies along the chain; modelled as one `F`, `H_k = H₀ + kF`. The
continuous form of the throw is `d/dt(H(t)v) = −∇L` with `Ḣ = F`, that is
`H v̇ + F v = −∇L`. The accretion acts as a friction `F` against the mass `H₀ + tF`: per unit mass
it vanishes like `1/t` on the deposit clock. The constant is the deposit's own `F`, not a chosen
time scale. The leap is the limit that spends the momentum at every deposit.

**The apex.** In the continuous form, `d/dt ½⟨v, Hv⟩ = −⟨∇L, v⟩ − ½⟨v, Fv⟩`: the kinetic reading
changes by the force's power on the actual velocity, less the accretion's loss. Over a move the
velocity is the whole carried move `ηD + c`, so the power is `−⟨∇L, ηD + c⟩`. Every trial lies on
one line, `w = D + c/η₀`, because the halvings scale impulse and coast together. The power test is
therefore the first trial's own first-order bound on its whole move (`first_order` on the
successor `stepped_source_coasting(η₁, (η₁/η₀)c)`, `η₁` the first step after the entry scale). A
negative upper end certifies that the motion falls, and only then is the coast carried. The
impulse's own slope refusal (`slope_refusal`) is read before the coast: a move whose impulse is
refused never reads its coast.

[derived] **Why not the coast alone.** #240 first read the bound along `c` alone, at the incumbent.
That splits the move into a coast followed by a kick, and lets the old line decide the release. A
leap lands past its own line's floor whenever it adopts the largest admitted step (m0's slope read,
§7), so the coast alone climbs and the move is released: the chain run under that rule (§6) is
then its own at-rest throw, move for move. A leap stopped exactly at its floor leaves
`⟨∇L, c⟩ = 0`, so the coast alone never descends at first order, while the whole move still does,
through `⟨∇L, ηD⟩ < 0`. That is the conjugate-direction case, the one where momentum pays.

[derived] **Why release at the apex.** The first-order bound's sign is shared along `w`, so where
the whole move climbs every halving on that line meets the same refused certificate. Carrying the
coast would spend the move's trials on steps that cannot be adopted. Releasing from rest keeps the
move the normal law's, whose impulse descends.

**The halvings.** The trials halve the whole carried move. A trial adopted at `2^(−j)` of the first
carries `2^(−j)` of the momentum, since its move is the next velocity. The halving is the time step:
the coast and the impulse shrink together. [agent-inferred] The impulse's own scaling within the
time step (an impulse is `η` and a coast is `h`, with `η = h²`) is not followed. One halving law
for the whole move keeps one sequence of trials and its per-move work bound, `LADDER_DEPTH` trials.

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

**The claim fixed first.** From the opening `c0.state` on gate A's requests (`order2`, seed
`2026093061`, 8 requests) under `lock-dec`:
- the 16-move throw chain ends with `L` below its control's at the same move count;
- and its held-out whole sections are at least the control's.

The control is the same `run.sh` with `coordinate` in place of `throw`, from the same `c0.state` and
requests. Both run under strict descent (`ReleaseExcursion::monotone`: `run.sh` sets no
`EXCURSION_CHECKPOINT`). So the comparison is like with like: the main line's Coordinate chain
adopts under #202's open run, which is a different rule. At the opening the Coordinate and Witness
moves both lie close to `G` and to `ΔE` (each step's `cos²` with `ΔE` in `[4095, 4096)/4096`, with
`G` in `[4069, 4070)/4096`).

Anything less is reported as what it measured: per move, `L`, solved decisions, whole sections and
stations right, the halvings at adoption, the flight's length and whether its coast was carried.

**Commands.**

```sh
cargo build --release -p holonics --example hnn_prediction
# The development read: the release (m0, at rest) and the first coast (m1), each under a loose
# per-move deadline that only bounds the read.
RAYON_NUM_THREADS=<threads> bash research/records/2026-10-02_THE_THROW_receipts/run.sh .local/throw-dev <loose ms> <loose s> 2
# The chain: the per-move bound is the larger of the development read's two moves.
RAYON_NUM_THREADS=<threads> bash research/records/2026-10-02_THE_THROW_receipts/run.sh .local/throw <per-move ms> <per-move deadline s>
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

**Threads.** `RAYON_NUM_THREADS` declares the probe's thread budget (19 by default, the PC's). On the
cloud host with 4 cores it is 4, and the per-move bound comes from the same host's development read.

**The development read** (cloud host, 4 cores, `RAYON_NUM_THREADS=4`, 3000 s a move; receipts in
`2026-10-02_THE_THROW_receipts/dev/`):

| Move | Flight in | Power along the coast | Coast | Trials | `L` after (nats) | Wall |
|---|---|---|---|---|---|---|
| m0 | at rest | none | none | `η 1/2` refused, `η 1/4` adopted | `[495714/4096, 495719/4096)` | 527242 ms |
| m1 | 1 move | `[21607/4096, 21609/4096)` | released from rest | `η 1/2` adopted | `[447159/4096, 447165/4096)` | 390167 ms |

The opening's `L` is `[500197/4096, 500203/4096)`. At m1 the comparison rises along the coast at first
order, so the first flight ends at its apex after one move and m1 is the leap from m0's state. m0's
read overlapped a 12 s Lean build.

**The projection, fixed at launch.** The unit is a trial. The two moves give a base of
`253092` ms and `137075` ms a trial (m1 at one trial, m0 at two). With `LADDER_DEPTH`'s 8 trials the
per-move bound is `253092 + 8 · 137075 = 1349692` ms, and the chain's deadline is
`16 · 1349692 = 21595072` ms, rounded up to `21596` s, launched as `timeout 21596` around
`run.sh .local/throw 1349692 1350` (each move's own deadline `1350` s is its bound rounded up).

**What the running chain measures.** It was launched at `7944b772`, under the coast-alone power
test. Its moves so far have all been released from rest (the power along the coast is
`[21607, 21609)/4096` at m1, `[16685, 16687)/4096` at m2 and `[59623, 59627)/4096` at m3). While
every move releases, it is the at-rest throw: `ρ` held, the same impulse. So it is the clean control
for the corrected chain, and against an at-rest control its difference is zero by construction, a
consequence of the coast-alone rule and not a reading of momentum. The corrected chain (the
whole-move power test) runs from the same `c0.state`, requests and strict descent, at 4 threads and
the same per-move bound. Its acceptance is the claim above, with this chain as the control. Its m1
state is byte-identical to the Coordinate control's m1; the Coordinate control left this path at m2
through `ρ` (it lowered `ρ` to `102139/131072`).

## 7. The floor along the line (after the development read)

**The read.** At m0's stored state, the plain pullback `G` (the descent covector on m0's own
sections) pairs positively with `E_c0 − E_m0`, with `cos²` in `[354, 355)/4096`. So
`⟨∇L(m0), ΔE_0⟩ > 0`: on its own sections m0 lies past the floor of its own line. On c0's fixed
sections the same line still fell at m0 (the mask's cells `[430625/4096, 430630/4096)` at `η 1/4`
and `[473652/4096, 473658/4096)` at `η 1/2`). The step's flipped commitments raised the released code
length to `[495714/4096, 495719/4096)`, and that jump is what turned the line (#207's crossing law).

**The law** [derived; the profile along the line is the hypothesis]. Along a line
`L(τ) = L(E + τw)`, with slope `s` at `τ = 0` and curvature `κ`:
- *Apex, `s ≥ 0`.* With `L` convex along the line, no point of it is lower
  (`convex_slope_le`, `coast_apex_no_floor_ahead`), so nothing on it can be adopted. Where `L` is
  not convex along the line this derives nothing.
- *Falling, `s < 0`.* The floor is at `τ* = −s/κ` (`coast_floor`); where `κ ≤ 0` the end is the floor
  (`coast_floor_at_end`). The secant `κ = 2(L(1) − L(0) − s)` is read from the line's own end
  (`coast_secant_curvature`), on the fixed mask, the same comparison the first-order bound reads.
- *Over enclosures.* The line falls on `[0, τ]` wherever `s + κτ ≤ 0`, for either sign of `κ`
  (`line_falls_to`). So with `s ≤ s⁺ < 0` and `κ ≤ κ⁺` the stop `min(1, −s⁺/κ⁺)`, the whole line
  where `κ⁺ ≤ 0`, is derived without certifying the sign of `κ`. #240's first floor stop carried the
  whole coast where `κ⁻ ≤ 0 < κ⁺`; that straddling case was chosen, and the derived stop replaces
  it.
- *What a stop dissipates.* The adopted move is the next velocity, so a move stopped at `τ` hands on
  `τ` of its momentum: `(1 − τ)` is dropped at the floor, a dissipation of the same kind as a
  halving's.

**Which line.** #240 first applied this along the coast alone (`MoveMetric::ThrowToFloor`, which
carried `min(1, τ*)·c`). That answers the coast-alone question §2 rejects, so it is removed. Under
the whole-move power test the line is the trials' own line `w`, and its floor is the ladder's own
floor: the main line is building it for the leap, from the secant of the trials the halvings
already read. It applies to the throw's line unchanged, and these lemmas are its Lean.

## 8. Where the Kinetic step turns from the normal direction (Q10)

The throw's impulse is the normal law's step `d`; `Kinetic`'s step is `M⁻¹AᵀK⁻¹w` with
`K = AM⁻¹Aᵀ` and `w = −F⁻¹c` (Q1: at `c0` its Euclidean `cos²` with `d` is `[37, 38)/4096`).

**The prediction** [agent-inferred, before the read]: the per-target weights turn little, since
Q1 reads the spread of `θ_t` in `[13, 14)`; the terms of one request share data features, their
covectors are rotations of one class covector, so the within-term blocks act near-diagonally and
the cross-term coupling carries the turn. The first step leaned on a Kantorovich bound,
`cos² ≥ 4κ/(κ + 1)²`, which holds for reweighting a vector's own coordinates. The weights here act
on terms whose pullbacks share rows of `E` and can cancel in `d = −Aᵀc`, so the bound does not
apply and a `θ_t` spread does not by itself bound their turn. The step with `μ_t = 1/θ_t` alone,
without `K`, is unread.

**The read** (runner 1, `research/runs/u6/cloud/q10/kinetic-coupling.txt` on
`claude/cloud-runs-pfo084` at `eeafdf7a`; at `c0`, Euclidean `cos²` against `d` over `4096`, the
M-metric readings within a few cells of each):

| `K` kept | `cos²` with `d` | Its solve |
|---|---|---|
| diagonal | `[662, 663)` | closed form |
| term blocks | `[852, 853)` | 64 blocks, converged after 5 iterates |
| request blocks | `[355, 356)` | 8 blocks: 4 converged after 38 to 40, 4 exhausted at 40 |
| joint | `[37, 38)` | exhausted at 320 iterates |

**What fails.** The diagonal alone does most of the turn, from `d` to `[662, 663)`. The within-term
coupling turns back toward `d` (`[852, 853)`), so the term blocks are not near-diagonal in effect.
The coupling within and then across requests finishes the turn. So the cross-term coupling does
carry the last part of the turn, but the reason given (near-diagonal term blocks, a weight that
turns little) is wrong at both steps.

**What the solve is.** The joint solve stops at 320 iterates without reaching its energy floor, so
the native `Kinetic` step is a truncated iterate. Its first iterate lies along `d`
(`[4068, 4069)`), and the `cos²` falls with every iterate until it settles: the last 63 iterates
all read `[37, 38)`. The step's direction is settled to the cell, but its length is the
truncated iterate's.

## 9. Verification

- `cargo check -p holonics --all-targets`: clean.
- The three throw tests (`a_coast_that_climbs_alone_is_carried_when_the_whole_move_falls` among
  them) and `the_kinetic_move_deposits_the_solve_and_keeps_every_guard`: see the PR.
- `bash tools/lean_check.sh HolonicsResearch.HNN.MoveDirection`: "Build completed successfully
  (8706 jobs)".
