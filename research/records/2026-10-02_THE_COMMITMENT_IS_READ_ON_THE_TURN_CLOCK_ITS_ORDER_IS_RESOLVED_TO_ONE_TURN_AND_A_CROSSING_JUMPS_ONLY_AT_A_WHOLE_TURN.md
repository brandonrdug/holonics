# The commitment is read on the turn clock: its order is resolved to one turn, and a crossing jumps only at a whole turn

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the theorems of `HolonicsResearch/HNN/OrderTemperature`; [derived from the code]
for §3; [agent-inferred] for the premise of §4 and the release law of §7, which no owner implements.
No run: §9 lists what the main line reads. Nothing in Rust changes here.

**Occasion.** Brandon asked why the temperature is fixed. The lock face reads each station's classes
as Gibbs shares at inverse temperature one, the growth over one turn (the Lean thread, today). The
[flip record](https://github.com/brandonrdug/holonics/blob/a7d404ea/research/records/2026-10-02_A_FLIP_IS_SET_BY_THE_LOCK_RULES_MARGIN_AND_NO_LAW_IN_THE_CHAIN_CERTIFIES_IT_BEFORE_THE_SUCCESSOR_IS_READ.md)
(on #207) located `m7`'s jump in the **order** in which stations commit. This record derives the
clock the order is read on, from the owners, and states what reading the order on it does to the
native move.

**Revision.** The first version of this record (PR #225, before this commit) read the order as an
average over the turn clock's origin, the three-arc split of §6, and drew from it a comparison with
no jump. The review asked whether the origin is a gauge. Read in the code (§3), it is not: every
station's turns are counted from one origin, the start of the read, which the receiver carries. The
ring's key, the other candidate origin, cancels from every reading of the release. So the order is
read at whole turns with that origin, the average over origins is not derived, and the claims built
on it are regraded (§6).

**Answer.**
1. One comparison reads at two temperatures. It reads a station's classes over one turn, and the
   order of the stations' commitments at zero temperature. Every jump the move cannot certify lives
   in the second (§1).
2. A station commits at an instant on the turn clock: the number of turns after which its lock
   face, read over that many turns, places its top within the receiver's grain (§2). That instant
   orders by the log ratio of top to runner. Read at whole turns, the station commits at turn
   `⌈t⌉`, a quantity of the growth over whole turns alone (`commit_turn_iff`).
3. **The origin is fixed and observable; the key is a gauge** (§3, from the code). The receiving
   ring's key, its declared initial configuration, enters the release only through differences of
   phase classes, so shifting it changes no reading. The whole-turn count has one origin, the start
   of the read, common to every station.
4. **The order is resolved to one turn, and it is a step order.** Stations that commit in the same
   whole turn commit together; otherwise the earlier turn commits first (§4). A crossing still
   jumps, from `C_A` through the co-present `C_C` to `C_B`, but only where a step carries some
   station's instant across a whole turn. At an incumbent where no instant is a whole number, every
   small enough step keeps the order, so the move is first order there and a negative slope is
   adopted by some halving (`wholeTurn_counts_eventually_const`, `fixed_order_halving_adopts`). A jump
   at every small step needs an instant exactly at a whole turn, an exact condition.
5. **The three-arc split is an average the clock does not supply** (§6). It is the whole-turn order
   averaged over the instants' position within the turn. It describes a population of pairs, the
   share of pairs `Δ` turns apart that a whole turn separates, not one comparison. Its continuity and
   first-order theorems hold for a release that smooths the order, which no reading licenses and no
   owner builds.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches **the helix**
(a commitment instant is a winding count plus a phase in the turn: the carry and the circle) and
**faces and placement** (the order in which committed data are placed beside later stations). The
pair, the cell holonomy, the tube and the tower thread stay attached: no contact, restriction or
transport changes.

## 0. The recorded failures this could repeat

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **An uncertified deposition step.** The whole-turn order changes what the comparison reads, not
  how a step is adopted. Every step is still re-read whole and adopted only on a certified decrease.
- **A refusal answered with a larger limit.** Nothing here lengthens a run or loosens a condition.
  The whole-turn order removes the near-tie flips that fall within one turn; a flip across a whole
  turn is still paid in full.
- **A located cause carried unrepaired.** The located cause is that the order is read finer than
  the clock reads it, the kind of defect the certified-lock rule repaired for cell ends. Its repair
  belongs in the order's owner (§7), not in the move.
- **Text run on its codec's grain.** The turn clock, the lock face and the grain are the receiving
  bank's, the same for text, image, acoustic and motor charts.
- **A design thought in the programming language.** The first version averaged over an origin
  because the formula looked like a mixture; the code's clock has one origin. The order is read on
  the clock the receiver has.

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

## 2. The commitment instant

[derived; `commitResidual_strictAnti`, `commit_instant_le`, `commitResidual_ge_one`, `commit_turn_iff`]

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
  (`r_y < 1`), `R` falls strictly with `n`. Its value at `n = 0` is the number of classes, above
  `2^τ − 1 < 1`, so it meets the level exactly once.
- **Below the threshold no station commits.** With `a_top ≤ 1`, `R(n) ≥ 1` at every `n ≥ 0`: the
  release's threshold, read as a commitment that never arrives.
- **A station whose residual lies below another's at every instant commits no later.**
- **The two-class instant.** With one rival and a top far above one, `R(n) ≈ r^n` and
  `t = c/ln(a_top/a_run)`, `c = −ln(2^τ − 1)`. At `τ = 1/16`, `c ∈ (3117/1000, 3118/1000)`. So
  stations commit in order of the log ratio `ln(a_top/a_run)`, the largest first. The flip record
  (§0) noted that the face orders by the log ratio while the release orders by the difference
  `a_top − a_runner`, and graded the difference the one term the face does not derive. The instant
  derives the log ratio, with the threshold term beside it: near the threshold, `a_top^(−n)` decays
  slowly and sets the instant.
- **At whole turns, the instant's ceiling** (`commit_turn_iff`). `R(n)` at a whole number `n` is read
  from `a^n`, the growth of the turn's monodromy taken `n` times; `R(n) ≤ 2^τ − 1` exactly when
  `⌈t⌉ ≤ n`. So a station read at whole turns commits at turn `⌈t⌉`.

## 3. The clock the code carries

[derived from the code; `turn_reading_section_free`] Two candidate origins for the turn clock, read
in the owners.

**The ring's key cancels from the release.** A ring's key is its declared initial configuration
(`hnn/keys.rs`, header): `Current::at_rest` starts the lift at it (`λ_g = initial`, `hnn/field.rs`),
and the phase class is `λ_g mod d_g` (`Current::phase`). Every quantity the release reads takes the
receiving ring's lift only through a difference of phase classes:
- a request datum taken at phase class `c` is read as `P^(−c) E M[c]` (`SourceMoment::moment_parts`)
  and rotated by `P^λ` (`open_parts`); `Ring::rotate` reads its power modulo the period
  (`Ring::split`), so the datum stands at rotation `λ − c ≡ phase − c`, its lag, which is also the
  lag `BankPlacement::of` weighs it at;
- station `j`'s class images are rotated by `λ − r_j` with `r_j = (phase + 1 + j) mod d`
  (`BankPlacement::of`), which is `−1 − j` modulo the period whatever the key;
- the turn is read in the passage's own time order, from the first station (age `−1`, tick `0`) to
  the newest request cell (`ring::turn`);
- a ring's own stepping never reads its own key (Lean `HNN/Moment.selective_position`).

So shifting the receiving ring's key, with the earlier rings' configurations held, changes no
placement, reading, gap, lock or released section. The key is observable elsewhere, through the
carry chain: a ring's key sets the instants it wraps, hence the next ring's stepping. Loop closure
locates a key only up to its rotor gauge orbit `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)`, and the published member
is a declared convention (`keys.rs`, "publication"; Lean `HNN/Keys.gauge_fix_unique`). Neither route
reaches the receiving face's commitment order.

**The whole-turn count has one origin, the start of the read.** `ReceivingBank::read_turn` reads
the turn's growth from the monodromy's characteristic polynomial (`growth_of`), which does not
depend on the crossing the product starts at (`turn_reading_section_free`). A count of whole turns
is `n` repetitions of that monodromy, read from `a^n`: it carries no section either, and every
station's count starts at the same `n = 0`. The present, the crossing every lag is measured from, is
carried by the placement. No origin of the whole-turn clock is unread, so no reading is owed an
average over origins.

**A count finer than a turn would need a section, and the code's is fixed too.** A reading at `k`
ticks into a turn is a partial product of crossing maps, whose spectrum depends on where the product
starts. The code starts it at the first station's crossing (`turn_monodromy`, tick `0`), measured
from the present. That origin is also carried, not gauge.

**What the code as built does.** The release iteration (`prediction::release_iteration`,
`LockOrder::Gap`) ranks stations by their gaps at each refinement; a refinement is not a turn, and
nothing counts turns or reads an instant. So under the current release no state depends on any turn
origin; the question of §4 is about the proposed whole-turn law.

## 4. The order at whole turns

**The premise.** [agent-inferred] The lock is read at whole turns. The reading `a_x` is a Floquet
multiplier, the map from one crossing of a section to the next crossing of the same section a turn
later; between those crossings the state is not compared with itself. The flip record states the
same principle for ticks: events closer than the clock's grain have no order on that clock. No owner
implements this (§3, last paragraph); it is the release law of §7.

[proved-derived; formal-checked] Read so, with `t_A`, `t_B` two stations' instants:

| Whole turns | The release |
|---|---|
| `⌈t_A⌉ < ⌈t_B⌉` | `A` commits, then `B` reads `A`'s datum (cost `C_A`) |
| `⌈t_A⌉ = ⌈t_B⌉` | `A` and `B` commit together (cost `C_C`) |
| `⌈t_A⌉ > ⌈t_B⌉` | `B` commits, then `A` reads `B`'s datum (cost `C_B`) |

- **Resolution one turn.** Two instants in the same whole turn have no order; this is the
  certified-lock rule's co-presence at the turn's grain. Two instants in different turns are
  ordered whole, at zero temperature. So the order's width is one turn, and it is a step, not a ramp.
- **Near ties within one turn do not flip.** Under `LockOrder::Gap`, two stations whose gaps nearly
  tie commit in an order that a small step can swap, the kind of jump `m7` met at every step size.
  Read at whole turns, two stations that commit in one turn are co-present before and after such a
  step, unless the step carries one of them across a whole turn: no jump.
- **A crossing jumps only at a whole turn** (`ceil_eventually_eq`,
  `wholeTurn_counts_eventually_const`). The instants move continuously with the readings. If no
  station's instant is a whole number at the incumbent, every small enough step leaves every
  station's turn, hence the order, unchanged. The comparison is then the fixed order's comparison,
  continuous, and the first-order certificate covers it.
- **A negative slope is adopted by some halving there** (`fixed_order_halving_adopts`). Where the
  order holds, the move's slope from the right is the fixed order's, and a negative slope is adopted
  at some halving of any step.
- **A jump at every small step needs an exact whole-turn instant.** At zero temperature a jump
  present at every small step refuses every halving (`jump_refuses_every_halving`). Under the
  whole-turn order that happens only when some `R(n) = 2^τ − 1` holds exactly at a whole `n` at the
  incumbent. The readings are exact enclosures, so the condition is decided, not estimated, and a
  state that meets it can be named before the step.
- **What a crossing still costs.** When a step does carry an instant across a whole turn, the order
  passes from `C_A` to `C_C` (or from `C_C` to `C_B`) at once. That jump is paid in full; the
  whole-turn order removes the flips within a turn, not the flips across one.

**What it does not do.** It does not bound how far a step moves an instant before the successor is
read: the segment bound on the readings' motion (the flip record's missing `Λ`) is still absent, so
how small "small enough" is cannot yet be certified in advance. It does not say the move reaches the
refit's basin or any held-out decision.

## 5. What it costs to read

[derived]
- **One release per refinement, as now.** Each refinement commits every station whose turn
  `⌈t⌉` is the smallest open one, together, and re-reads. A pair is never released in two orders.
- **The distance to the next whole turn.** Each station's `⌈t⌉ − t` at the incumbent is the
  margin a step must not cross. With `t′ = −R_a·a′/R_n` (the readings' variation over the residual's
  fall per turn, from the candidate covectors already read at the decision sites), `(⌈t⌉ − t)/t′`
  is the first-order step at which the order would change.
- **Exact arithmetic.** The instants are logarithms of readings, so each is an enclosure with exact
  endpoints, and `⌈t⌉` is read exactly unless the enclosure contains a whole number, which is the
  exact-instant case above. No float enters.

## 6. The three-arc split: what it approximates

[proved-derived for the kernel; regraded] The first version read the order through the kernel

```text
Φ = clamp(Δ) C_A + max(0, 1 − |Δ|) C_C + clamp(−Δ) C_B,      Δ = t_B − t_A in turns,
```

as an average over a turn origin taken uniform on the circle (`aheadShare`, `copresentShare`,
`shares_sum`, `copresentShare_eq`, `aheadShare_of_one_le`, `aheadShare_lipschitz`). §3 shows the
code has no unread origin, so that average is not a symmetry requirement. What it is:
- **The whole-turn order averaged over the pair's position in the turn.** For a pair `Δ` turns
  apart, `clamp(Δ)` is the share of positions at which a whole turn falls between the two instants
  (with `p` crossings a turn, within `1/p` of it: `tick_count_near`, `tick_share_near`). Over a
  population of pairs spread through the turn, it is the share the whole-turn order separates.
- **Its theorems are about a smoothed release.** The kernel is continuous (`threeOrder_continuous`,
  `orderMixture_continuous`), its slope carries the anticipation `p′ μ′ (C_A − C_B)`
  (`orderMixture_hasDerivAt`, `anticipation_pos_iff`), the anticipation integrates to the jump
  (`anticipation_integral`), and a negative slope is adopted by some halving
  (`halving_adopts_of_neg_slope`). These hold for a release whose comparison is that average, one that
  releases each pair in all three orders and weighs them. No reading licenses the weights, and no
  owner builds that release. The adoption result that holds for the whole-turn order is §4's, which
  needs no average.
- **What survives as mathematics.** Sharpening the kernel returns the zero-temperature order off
  the crossing (`occupation_sharpens_pos`, `occupation_sharpens_neg`, `orderMixture_sharpens`), and
  an uncertainty of `w` turns in `Δ` leaves at most `w` times the larger cost unread
  (`orderMixture_resolution`). Both are statements about the kernel, kept for a receiver whose own
  readings left the pair's position in the turn unresolved; this receiver's do not.

## 7. The release's order law (proposed; changes behaviour)

[agent-inferred; not built] The consistent release reads the order on the same clock as the
comparison: each station commits at turn `⌈t⌉` of its instant, counted from the start of the read,
and stations that commit in one turn commit together. The current rule, largest gap first, is that
law's proxy: it orders by the difference instead of the log ratio and resolves the order inside the
turn, finer than the clock reads. Changing it changes HNN behaviour and needs campaign 1's held-out
read before it merges.

## 8. The memory length and the turn

[agent-inferred] Brandon's question also touched the memory length `ρ`. The founding's ceiling on
`ρ` is a statement about the same clock from the storage's side
([the joined move](2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md) §1):
the phase record identifies a datum's age only within one turn, so a datum one turn old must weigh at
most one chart unit, `ρ^d ≤ 2^(−L_ν)`.
- The storage reads the **phase** within the turn and not the count of turns: a turn-old datum would
  alias onto the present.
- The lock reads the **count** of turns and not the phase within the turn: commitments in one turn
  are co-present.

These are the helix's two parts, the circle and the carry. So the order's resolution and `ρ`'s
ceiling are two faces of one fact, that the turn is the receiving clock's grain. They fix different
quantities: the order's width and `ρ`'s upper bound. Neither fixes `ρ`'s value below the ceiling.

## 9. What the main line reads

All at `m7`'s incumbent (the state whose move was refused at every step size from `1/16` to `1/2048`)
on request 3, which carries the flip, with the pair that swaps commitment order:
1. **The pair's turns.** Each station's `a_top` and rivals' readings, the instants `t_A`, `t_B` at
   `τ = 1/16` bit (§2), and `⌈t_A⌉`, `⌈t_B⌉` at the incumbent and at the `1/2048` successor.
   - If the two turns are equal at both, the pair is co-present on both sides of the step, and the
     whole-turn order has no flip there: `m7`'s jump is an artefact of ordering inside the turn.
   - If a turn changes along the step, the step carries an instant across a whole turn; read the
     distance `⌈t⌉ − t` at the incumbent against the step's `t′`.
2. **The co-present release.** `C_C`: the comparison on request 3 with the pair committed together.
   With `C_A` (the incumbent) and `C_B` (the swapped order, `C_B − C_A = 34038/4096` at the
   successor), this is what the whole-turn release reads in place of the swap.

Read 1 decides whether the whole-turn order reaches `m7`'s flip at all.

## 10. Verification

- `lean/HolonicsResearch/HNN/OrderTemperature.lean` imports only Mathlib and builds in the repository
  with `bash tools/lean_check.sh HolonicsResearch.HNN.OrderTemperature` with no errors, warnings or
  `sorry` (receipt in the PR).
- The code reading of §3 was made in `hnn/field.rs` (`Current::at_rest`, `Current::phase`,
  `Ring::rotate`, `Ring::split`), `hnn/moment.rs` (`open_parts`, `moment_parts`), `hnn/prediction.rs`
  (`BankPlacement::of`, `bank_release`, `release_iteration`, `LockOrder`), `hnn/ring.rs`
  (`read_turn`, `turn_monodromy`, `turn`, `growth_of`) and `hnn/keys.rs` (header).
- No Rust changed, so no cargo gate applies.
- Owed (#62): the key's cancellation as a theorem on the placement (here read from the owners, not
  formalised); the instants' continuity in the constitution, which §4 takes as a hypothesis; the
  kernel of §6 as a measure on positions in the turn (derived by the boundary count, not formalised);
  and the release law of §7, if built.
