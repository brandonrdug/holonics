# A flip is set by the lock rule's margin, and no law in the chain certifies it before the successor is read

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the statements cited to `HNN/ExecutedComparison` §13 and §14; [measured] for the
main line's numbers in §4a; [derived] from the owners'
code where marked; [agent-inferred] where marked, the lock rule of §5 among them. No run here. The
lock rule and the order term that reads it change in Rust (§5).
Follows [the release's record](2026-10-02_THE_RELEASE_GUARD_CERTIFIES_THE_FIXED_MASK_AND_CHARGES_THE_FLIP_OVER_A_WINDOW.md)
(its §1 holds `m7`'s measurement: at every step size from `η = 1/16` to `1/2048` the own release reads
`34038/4096` nats above the fixed mask at the same `E`).

The question: what sets a flip's sign and size, expressed through the lock rule's margin and the
comparison's values at that decision; and whether the native move can certify the flip it causes,
by a first-order bound on the own release along the move or by the lock rule's own law, instead of
paying for it afterwards.

**Answer.** A flip happens where a lock rule margin crosses zero. Its size and sign are the comparison
re-read on the successor's sections against the incumbent's. Neither is certified before the
successor's release is read. The first order predicts a crossing but cannot bound one. The lock rule
decides on cell ends whose place inside a cell the enclosure does not carry. The chain has no bound
on how far a reading moves over a step's segment. **No law in the chain certifies a flip before the
successor is read.** It is read exactly when the successor is read, at each step size, and it is
paid over a run of steps between two endpoint states (Lean §12; the release's record).

The main line's first read (§4a) placed `m7`'s flip in the lock rule's ranking of gaps. Its replay
(§5) finds a true crossing, certain at both ends: the pair is certified one way at the incumbent by
about 140 cell widths and the other way at the successor by about 20. The rule of §5 does not
address it. §5 gives the rule that locks together every station the readings do not
certify below the largest gap. No move can swap a certified order without the readings crossing.
The rule is inferred from the release's own reading of its other decisions; no owner states that
reading for the gap order. The comparison's order term reads the same two ends, so the release and
the term keep one law.

## 0. The physical statement

[derived where cited; agent-inferred where marked] Every term below names a quantity of the
receiving bank or a process it undergoes.

- **A station is a crossing on the receiving ring's helix, and a candidate is a class placed
  there.** A station is tick `τ + 1 + j` of the receiving ring's clock (`hnn::prediction`, "The
  section"), and a candidate is a class `x` of the exterior chart placed at that tick ("the
  candidates"). The candidate's reading `a_x` is the bank's growth over one turn of the passage
  with that class placed (`hnn::ring::ReceivingBank::read_turn`): the largest member's dominant
  Floquet multiplier modulus. A member reads the turn only when its pump's period divides it, so
  one turn can hold several pump periods. The receiver knows the reading only as an enclosure
  `[L, U]` of relative width at most `2^(−g)` at its upper end. That width is the receiver's
  resolution; nothing finer is a reading.
- **A lock is the station committing to one class.** Past the threshold (`a > 1`), a class whose
  multiplier exceeds every rival's outgrows them every turn. The release commits the station to
  that class and places its datum, all or nothing. [derived] That is the lock face at zero
  temperature. The face (`ExecutedComparison.lockFace`, `ℓ = log((1+a+r)/a)`) is `−log θ_t` with
  shares `θ_t = a_t/(1 + Σ_y a_y)`, the resting state at weight one. Raising each weight to `1/T`
  gives `θ_x = a_x^(1/T)/(1 + Σ_y a_y^(1/T))`. As `T → 0` the shares go to the top class when
  `a_top > 1`, to rest when every `a_x < 1`, and split evenly among tied tops. That gives both the
  threshold `a > 1` and, at one station, tied classes sharing the commitment (`ParametronLock`:
  "the threshold is this face at zero temperature"). The release keeps only that limit. Stations
  committing together is a different statement, the rule across stations that §5 infers.
- **The gap is the dominant class's excess multiplier**, `g = a_top − a_runner`: how much more per
  turn the dominant class grows than its strongest rival. The readings enclose it between its
  **certain gap** `lo = L_top − max U` (the least value the readings allow) and its **upper end**
  `hi = U_top − max L` (the greatest). Stations commit in order of the gap, the largest first, and
  each commitment changes the section the later stations read: a placed datum enters every later
  station's storage. [agent-inferred] The face's own variable is the log ratio: two shares stand in
  the ratio `(a_top/a_runner)^(1/T)`, so the face orders by `ln(a_top/a_runner)`. Ordering by the
  difference `a_top − a_runner` is the release's existing law, and it is the one term here the face
  does not derive.
- **The comparison is a code length.** Each station's term `ℓ = −log θ_t` is the code length, in
  nats, of its target under the lock's shares, and the comparison sums it over the decisions.
  Exactly, `−log θ_t = D(δ_t‖θ)`: the relative entropy of the target state over the lock's
  equilibrium shares. It is a code length, not an energy. Reading it as a free energy in units of
  `k_B T` needs a map from cross-entropy to the Holons' storage and work that is not derived; the one
  derived case (Astra's) is that at a fixed temperature the change in code length equals the force
  less its average. So the jumps below are jumps in code length, and the map is owed in #62. It is
  read on the released sections, so it depends on the commitments.
- **Why a decision changes discontinuously.** The commitment is all or nothing, so the released
  sections are piecewise constant in the constitution. They change only where two gaps change order
  or a multiplier crosses the threshold. Across such a boundary the stations read different placed
  sections, and the code length jumps by `J` (§2). The jump is set by which data are placed beside
  which, not by how far the constitution moved, so it does not shrink with the step. [derived] This
  is a zero-temperature first-order switch, a level crossing. At temperature `T` the lock's log mass
  `T log(1 + Σ_x a_x^(1/T))` tends to `log max(1, a_top)`: continuous in the multipliers, with a
  kink where the top changes. The code length is not that quantity. It is read on the sections the
  commitments produced, so it jumps where the selection switches, as an order parameter does across
  a coexistence line. At a finite temperature the commitment would be a continuous occupation and
  the jump a steep but continuous change: the same transition rounded by temperature. The chain
  runs no finite-temperature release, and this record proposes none.
- **Why stations whose gaps the readings cannot order commit together.** Two gaps whose enclosures
  overlap have no order this receiver can measure. Committing one first would make the release
  depend on where each multiplier lies inside its cell, which no reading carries. So the receiver
  treats the two commitments as simultaneous. Events its resolution cannot order are co-present for
  it, as two events closer than one tick have no order on that clock. They are taken apart only
  when the constitution moves the multipliers until the enclosures no longer overlap. Then the
  receiver resolves their order. An order it has resolved reverses only if the true gaps cross
  (§5, `certified_order_needs_crossing`). What can still switch is a co-present pair separating.
- **What is compared, between which two states.** The code length at the incumbent state and at
  the successor state, each read through its own commitments. Its change splits (`own_telescopes`)
  into the change with the incumbent's commitments held, which is continuous and certified at first
  order, and the switching jump `J`, which no bound on the step certifies (§3). Where the jump is
  paid, over a run of steps between two endpoint states, is the release's record.

## 1. Where a decision changes: the lock rule's margin

[derived; `hnn::prediction::bank_release`, `hnn::ring::{growth_of, bisect}`]
- **Each reading is a cell.** A candidate's reading `a` (the joint spectral radius over the bank's
  members) is enclosed by `bisect`. The bracket is a dyadic `[2^k, 2^(k+1)]`, bisected while its
  width exceeds `upper · 2^(−grain)`. So `L` and `U` are dyadic cut points with width
  `w ≤ U · 2^(−grain)`. They are piecewise constant in the storage, changing only where the
  reading crosses a cut. The rounded first attempt (`ATTAINMENT_BITS`) is kept only when its cell
  contains the exact root, so its ends are cut points of the same kind.
- **Each station has a gap.** At a refinement every open station's top is its largest `L`. It is
  eligible when its `L` exceeds every rival's `U` and exceeds one (locked). Its gap is
  `g_j = L_top − U_runner`, which lies in `(a_top − a_runner − w_top − w_runner, a_top − a_runner]`.
- **The rule.** The eligible stations of the strictly largest gap lock together, ties together.
- **The margin at a refinement** has three parts:
  - `μ = g_(1) − g_(2)`, the largest gap less the next (zero at a tie);
  - each locked station's threshold margin `L_top − 1`;
  - each locked station's own gap `g_(1)` (its eligibility).
- **A decision changes exactly where a visible margin changes sign or a tie splits.** The
  refinement's lock set (who locks, with what class) is a function of the visible gaps alone.
- **The visible and true margins differ by less than four cells.** The visible `μ` differs from the
  true difference `(a_top1 − a_run1) − (a_top2 − a_run2)` by less than the four widths
  `w_top1 + w_run1 + w_top2 + w_run2`.

## 2. A flip's cost through the comparison's values

[derived] Notation:
- `S_r` is the incumbent's placed cells before refinement `r`, `d(j)` the refinement that locks
  station `j`, and `r*` the last refinement whose placed cells all equal their targets.
- `s(j) = min(d(j), r*)` is `j`'s reading site.
- `ℓ_j(Θ; S)` is `j`'s lock face read at state `Θ` with section `S`.
- Primes mark the successor `Θ′`.

At `Θ′` the fixed mask reads `Σ_j ℓ_j(Θ′; S_(s(j)))` and the own release reads
`Σ_j ℓ_j(Θ′; S′_(s′(j)))`. The flip is their difference (`own_telescopes`'s second sum):

`J = Σ_j [ℓ_j(Θ′; S′_(s′(j))) − ℓ_j(Θ′; S_(s(j)))]`,

plus, under `Composition::LockOrder`, the order term at `r*′` less the order term at `r*`.

Let `r₀` be the first refinement where the successor's lock set differs. Every station whose sites
both lie before `r₀` reads the same section, so **`J` sums only over the stations open at `r₀`**.
Every section the decisions read holds only correct cells, by `r*`'s definition. For correct cells
`T` placed beside a section `S`, write
`V_j(T | S) = ℓ_j(Θ′; S) − ℓ_j(Θ′; S ∪ T)` for **the context value of `T` to `j`**. It is
positive when the placed data lower `j`'s term. The flip at `r₀` is one of three kinds:

| Kind at `r₀` | Successor's `r*′` | `J` |
|---|---|---|
| **A, a wrong lock earlier**: the incumbent locked a right station, the successor a wrong one | `r₀` | `Σ_(j open at r₀) V_j(S_(s(j)) ∖ S_(r₀) | S_(r₀))` |
| **B, a wrong lock removed**: the incumbent locked wrong at `r₀ = r*`, the successor right | `> r₀` | `−Σ_(j open at r₀) V_j(S′_(s′(j)) ∖ S_(r₀) | S_(r₀))` |
| **C, an order change**: right stations both, a different set (a split tie among them) | unchanged or later | `Σ_j [ℓ_j(Θ′; S′_(s′(j))) − ℓ_j(Θ′; S_(s(j)))]`, neither section containing the other |

- **Kind A.** Every station open at `r₀` is read at `r₀` with less correct context, so `J` is the
  value of the dropped correct locks. The newly wrong station's own term is past the solved level,
  because its wrong top's reading exceeds the target's (`lockFace_ge_log_two_of_rival`).
- **Kind B** is kind A reversed: `J` is minus the value of the gained context.
- **A split tie of two right stations** `a`, `b` (kind C), with `b` locking at the next refinement
  and the later refinements unchanged, costs `J = −V_b({a} | S_(r₀))`: the value of `a`'s datum to
  `b`.

**What sets the sign.** A flip's sign is the sign of a context value: whether correct placed data
lower a station's term. No law in the chain signs it:
- placing a datum adds `w_j(k) P^(r_k) E e_(t_k)` to `j`'s storage and renormalizes every weight;
- the reading is a spectral radius of the resulting monodromy;
- neither is monotone in the placed data.

**What sets the size.** Each `V_j` is a difference of two exact comparison readings at `Θ′`, and the
trial already reads both: the fixed mask at the trial, and the own release at the trial.

**A flip does not scale with the step.** The size `J` belongs to the sections, not to `η`. It stays
as `η → 0` while the fixed mask's certified decrease falls in proportion to `η`. That is why halving
cannot pay for it, which is §12's `one_move_closes_iff` read from the other side.

## 2b. A true crossing: located at first order, paid at zeroth order

The main line's replay finds `m7`'s flip a true crossing of two certain gaps (§5). The released
classes do not change. The jump comes from later stations being read with different data placed
before them. This section states what such a crossing costs and what bounds it.

**The comparison along a step jumps at each crossing.** [derived; §1, §2] Inside a region of constitutions where
the commitment order is fixed, the comparison is read on fixed sections and is continuous in the
constitution; the first-order law certifies it where its condition holds. Where two certain gaps
cross, the order changes and the comparison jumps by

```text
J_c = Σ_(j∈D) [ℓ_j(Θ_c; S′_j) − ℓ_j(Θ_c; S_j)]
      (+ under Composition::LockOrder, the order term on S′ less the order term on S)
```

with both sums read at the **same** constitution `Θ_c`, and `D` the stations read with different
placed data (those open at the first changed refinement, §2). `Θ_c` is the first carried state past
the crossing's cut. It is read with both commitment orders: the own release (`S′`) against the
fixed mask (`S`), which is exactly what the trial's `change` field reads there. Two carried states
on either side of the cut would not do: they are two constitutions, and their difference is the
jump plus that cut's continuous move. Only the order of commitment differs inside `J_c`. So `J_c`
is a property of the crossing, not of the step that reaches it: it stays as the step shrinks onto
the crossing. The location is a first-order event (the margin moves at a rate the first-order
readings give; at `m7` it crosses at `731/840` of the step under linear motion), and the cost is a
zeroth-order one, a jump in the code length.

**What bounds the lock faces' part of the cost.** [proved-derived; formal-checked] A lock face
`ℓ = log(1 + a + r) − log a` moves by at most twice its readings' largest log change
(`lockFace_sub_abs_le`). If station `j`'s target reading and rivals' sum change by at most a factor
`e^(δ_j)` between its two contexts, then the lock faces' sum obeys

```text
|Σ_(j∈D) [ℓ_j(Θ_c; S′_j) − ℓ_j(Θ_c; S_j)]| ≤ 2 Σ_(j∈D) δ_j          (crossing_cost_le)
```

Under `Composition::LockOrder` the order term's change between the two orders is not covered by this
bound; it is read beside it. Physically `δ_j` is the largest change in a class's growth exponent per
turn that the different placed data cause at station `j`.

The theorem holds at any constitution, so it applies at `m7`'s 1/2048 successor `Θ′`. There §2's
`J = +33987/4096` is the own release against the fixed mask, both read at `Θ′`. With the order
term's part taken off first, `Σ_(j∈D) δ_j` at `Θ′` is at least half of what remains (at least
`33987/8192` when that part is zero). `J` at `Θ′` is not `J_c`: the two differ by how each order's
comparison changes between `Θ_c` and `Θ′`.

**What the chain owns before the crossing.**
- [derived, from the lattice floor; its Lean statement is owed to the release follow-up (#62)] With
  every reading at least the floor `ρ₀`, each face is at most `log((1 + A_j)/ρ₀)`, `A_j` the
  station's readings' sum in that context. `A_j` changes between the two contexts, so each station's
  bound is `log((1 + max(A_j, A′_j))/ρ₀)` and the lock faces' part of `|J_c|` is at most their sum
  over `D`: finite, a priori, and far from tight.
- No owner bounds `δ_j` before the crossing is read. The bound would come from #62's segment bound.
  A placed datum adds a finite-rank term to the storage, and a reading is the spectral radius of a
  monodromy that is not self-adjoint. The change in placed data at a crossing is finite, not small,
  so that route needs a path of data from one context to the other along which the multipliers
  never coalesce, not only Lipschitz motion of the radius at the two ends.
- No law signs `J_c` (§2: context values are not monotone in the placed data).

So a crossing's cost is **not** bounded before it is read, except by the floor's coarse bound. Once
the crossing is located it is read exactly, at `Θ_c` with both orders.

**The treatment that follows.** [agent-inferred; from `own_telescopes`, §12's `one_move_closes_iff`
and the carried-cuts record's step law (#211); nothing here is built] With the crossing located at
its cut:
1. **Stop before the crossing.** The last carried state before the cut has the incumbent's commitments,
   so its decrease is the fixed mask's. It is certified at first order where the first-order
   certificate's condition holds at that state's step size; no run is needed.
2. **Cross when the jump is negative.** If `J_c` plus the continuous change across the cut is
   negative, the crossing is a decrease read exactly, taken in one move.
3. **A positive jump: one move or a run.** One move is accepted across crossings exactly when its
   continuous decrease from its start to its end exceeds the sum of the jumps of every crossing it
   passes (§12, `one_move_closes_iff`). A move whose certified decrease up to the crossing exceeds
   `J_c` pays it in one move. The decrease grows with the step and a crossing's jump does not, so a
   short move onto a positive jump does not pay it, and a longer one does if its decrease outgrows
   every jump it passes. At `m7` the step `1/16` certifies `d = 33562/4096` against a jump of
   `74106/4096`, but that step passes more crossings than the one at `1/2048`; which crossings it passes
   is the main line's measurement on the cut list. Only when no single move pays the jump is it
   crossed by a run of moves that must close one receiver grain below its opening state (the
   release's rule). The run's upper length (`8` in the chain) is a chosen bound on work, not a law,
   and closing a grain below the opening is necessary for that descent, not sufficient for
   anything further.

So the run-of-moves acceptance is the treatment for a positive jump that no single move pays. It is
not the only treatment of a crossing. A located crossing gives a certified alternative: descend to
the crossing and stop, or cross it in one move when the move pays it. A positive jump is a rise in code length
between two commitment orders, which a zero-temperature release crosses only by an excursion, the
run of moves with its height `h`. Whether to cross it is the endpoint comparison between the two states
the run joins, and nothing in the chain decides that sooner.

## 3. Whether the move can certify the flip it causes

### 3a. By a first-order bound on the own release: no

- **A flip present at every small step defeats every first-order bound**
  (`flip_defeats_first_order`). If `own η = g η + J` on `(0, δ)` with `J > 0`, `own 0 = g 0` and `g`
  right-continuous, then for every slope `s` and curvature `K` some step has
  `own 0 − η s + K η² < own η`.
- **A flip at a positive `η_c` needs a curvature constant of at least its cost over `η_c²`**
  (`flip_curvature_lower`): `J − η_c (s₁ − s) ≤ K η_c²`. Here `s₁` bounds the continuous part's fall.
  At `m7` the flip is present at `η = 1/2048` among step sizes halved from `1/16`. So its `η_c` lies
  at or below `1/2048`, and a smooth bound through it would need
  `K ≥ 34038 · 2^10 − 2048 (s₁ − s)` nats per unit step squared, on a comparison whose
  first-order slope the release reads at order one. No such constant is in the chain, and none
  would be a property of the comparison rather than of the flip.

### 3b. By the lock rule's own law: only with a bound the chain does not have

- **A margin moving at a bounded rate certifies no flip within it** (`no_flip_within_margin`). If
  `|μ η − μ 0| ≤ Λ η`, then `μ η > 0` wherever `Λ η < μ 0`. This is the lock rule's law that would
  certify a flip-free step: `η < μ/Λ` at every refinement up to `r*`.
- **It needs two things.** The first is `Λ`, the rate at which a true reading can move over the
  step's segment. The second is the true margin, which the visible one bounds only to within four
  cell widths (§1).
- **The visible end gives no handle on when it moves.** It holds until the true reading reaches its
  cell's cut, and moves there (`cell_holds_until_cut`, `cell_moves_at_cut`). The step to that cut
  lies anywhere in `(0, w/v]` for a reading moving at rate `v` (`cut_within_cell`). Where in that
  range is set by the reading's place inside its cell, which the enclosure does not carry.
- **So a margin within the summed cell widths can flip at an arbitrarily small step.** That includes
  a tie, which the rule locks together.
- What the chain has:
  - the visible margins at every refinement (the release's eligible gaps, `OrderReading`);
  - the readings' first variation (the candidate covectors, computed today at the decision sites
    and, under `LockOrder`, the order term's gaps at `r*`). The same law would give each gap's slope
    at `r₀`, so the first order can **predict** a crossing at `η ≈ μ/(−μ′)`;
  - a finer bisection of the incumbent's readings, which would place each true reading inside its
    cell.
- **What it lacks is `Λ`: a bound on a reading's motion over a segment.**
  - A simple root's derivative is bounded at a point by the root's separation from its neighbours.
    The covector refuses a collision only at a point.
  - The parked readings' curvature term reads `∇²r` at the incumbent. That predicts the second
    order, but it bounds nothing over the segment.
  - No owner bounds a root's separation, or the monodromy's variation, over `[Θ, Θ′]`.
- **The order term is the closest existing law** (`Composition::LockOrder`). It is the comparison's
  term on the same margin, the right station's certain gap against the wrong ones' upper ends at `r*`
  (§5). Descending it
  pushes kind-A margins away from zero at first order. It is still a term to descend, not a
  certificate. Under `Reading::Decisions` it is read only at `r*`, so a kind-A flip at `r₀ < r*` is
  outside it.

**So no law in the chain certifies a flip before the successor is read.** The flip is certified
exactly when the successor is read, which reads both comparisons. It is paid over a run of steps
between two endpoint states, or that run is refused.
[agent-inferred] Supplying `Λ` would take a new owner: a segment bound on the root separation of each
read monodromy. Until it exists, a flip-free step can be predicted but not certified.

## 4. What the main line's per-decision read decides

[agent-inferred] The `m7` flip persists at every step size down to `1/2048`. That is what §3a describes
when a margin lies within the summed cell widths (or a tie), or when `μ/|μ′|` is below `1/2048`.
Three readings at the incumbent of `m7`'s first refused move settle which:
1. **The first changed refinement.** `r₀`, its kind (A, B or C), and the stations it re-reads.
2. **The margin at `r₀`.** Its visible value `μ` and the four cell widths. A margin within the widths
   means no step avoids the flip. Above them, the gap covectors at `r₀` give the predicted crossing
   `μ/(−μ′)`.
3. **The cost per station.** `J` per station as `V_j`. If kind A, the `34038/4096` total is the value
   of the correct locks dropped between `r₀` and each station's site.

If it is a kind-A flip within the cell widths, the flip is set by the release's grain and not by the
step. No step size, no length of the run that pays it, and no first-order bound reaches it. What
remains is to change the commitment or the grain it is read at, not the condition on the successor.

### 4a. The main line's read: a swap of the lock order (kind C)

[measured, by the main line, cited] At `η = 1/2048`, `m7`'s flip is one decision chain in one
request, and it is of kind C, not the kind A this record expected:
- **Request 3 carries it.** Request 3 rises from `43957/4096` to `77944/4096` (`+33987/4096`). The
  other seven requests fall by `306/4096` in total.
- **The released section is unchanged.** It reads `[3,3,3,3,3,3,3,3]` before and after, wrong at six
  of eight stations: a degenerate release.
- **The lock order changes.** The ranking of gaps swaps which station locks first. Six
  stations are read at different partial sections, and three terms' tops flip (stations 3, 6, 7).
- **Per station** (each a lower end over `4096`, good to within `6/4096`): `ℓ` moves
  - station 1 by `+2742`, station 3 by `+6100`, station 4 by `+11986`, station 6 by `+9452`,
    station 7 by `+3815`;
  - station 2 by `−105`, station 0 by `−4`, station 5 by `−2`.
- **Per step size**, as (realized fixed-mask decrease `d`, flip, own less incumbent), each over `4096`:

  | `η` | `d` | flip | own less incumbent |
  |---|---|---|---|
  | `1/16` | `33562` | `74106` | `40544` |
  | `1/32` | `20269` | `45891` | `25622` |
  | `1/64` | `10853` | `34325` | `23472` |
  | `1/128` | `5523` | `34174` | `28651` |
  | `1/256` | `2804` | `34100` | `31296` |
  | `1/512` | `1419` | `34065` | `32646` |
  | `1/1024` | `714` | `34047` | `33333` |
  | `1/2048` | `359` | `34038` | `33679` |

  Below `1/64` the flip is a fixed cost while `d` halves with `η`, as §2 says a flip must. `m6`
  adopted at `1/2048` (`d = 361`, no flip) and flipped at `1/1024`.
- **The float path's excursions are not flips of this kind.** Its flip part per ten steps has
  both signs and nets negative, and per term is at most `227/4096`, against `m7`'s about
  `532/4096`. Its rises are continuous: minibatch steps on other requests raise its own read mask.

So the flip sits in the lock rule's ranking of gaps, which §1 shows is read on cell ends. §5 takes
the rule itself, and its replay at `m7` finds a true crossing.

## 5. The lock order the readings certify

**The defect.**
- Each eligible station's true gap `a_top − max_(x≠top) a_x` is enclosed by its **certain gap**
  `lo = L_top − max U` (what the release reads) and its **upper end** `hi = U_top − max L`.
- The rule as it stood locked only the strictly largest certain gap.
- So two stations whose gap enclosures overlap were ordered by where their cells' cuts fell, not by
  their readings. A move too small to change any reading's order could still swap them. (`m7`'s
  swap is not this case: its pair crosses, certified at both ends, §5's replay.)

**The rule, in the lock rule's owner, with no second rule.** A station locks when no station's
certain gap exceeds its upper end: every station the readings do not certify below the largest
locks with it. On exact readings (upper end = certain gap) this is the largest gap with its ties, the rule as
it stood. What follows (Lean §14, `section CertifiedLock`):
- **It always locks something.** The station of the largest certain gap locks
  (`certifiedLock_largest`), so a refinement with an eligible station locks a nonempty set.
  `decisions_release_the_section` (§8) holds for any nonempty lock set, so it applies unchanged.
- **The true largest gap always locks** (`leader_locks`).
- **A station that locks alone has the strictly largest true gap** (`lone_lock_is_largest`).
- **No move swaps a certified order without a crossing** (`certified_order_needs_crossing`): if `j`
  is certified below `k` at one state and locks alone at another, their true gaps crossed between.
- **What remains possible is a split.** An uncertified pair locked together can come apart when a
  move certifies one above the other. Its cost is the split's (§2, kind C: the value of the first
  datum to the second).

**Forced or chosen.** [agent-inferred] Inferred from the release's own reading of its other
decisions; no owner states that reading for the gap order, so the rule is graded agent-inferred
here and in Lean (`certifiedLock`):
- A top exceeds its rivals only when its `L` exceeds every rival's `U`, and a station locks only
  when its `L` exceeds one. Both are certified orderings of enclosures.
- An ordering the enclosures do not certify is read plural: "no positive gap is a plural reading",
  "ties lock together".
- The gap ranking was the one decision that compared bare cell ends as if they were readings.
- Reading it the same way leaves nothing further to choose. The comparison `≥` (upper end meeting the largest)
  keeps a possible true tie together, as the exact rule does. The cells are the receiver's declared
  grain.

[agent-inferred] The one alternative, refining the cells until overlapping gaps order, changes the
receiver's grain, which the release does not own. So it is refused.

**The order term reads the same ends.** The comparison's order term (`hnn::executed::OrderTerm`,
`Composition::LockOrder`) read the right station's certain gap against the wrong stations' certain
gaps: `solved` was `lo_r > Σ_(E∖R) lo`. Under the rule above a wrong station `j` locks whenever its
upper end meets the largest certain gap, so that `solved` no longer certified that no wrong station
locks. The term now reads each wrong station at its upper end and the right station at its certain
gap:
`ℓ_o = log((lo_r + Σ_(E∖R) hi)/lo_r)`, solved exactly when `lo_r > Σ_(E∖R) hi`. Each upper end is
nonnegative (an eligible top exceeds every rival), so solved gives `lo_r > hi_j ≥ lo_j` for every
wrong `j`: none locks (Lean `order_solved_locks_no_wrong`). Each wrong station's covector returns
through its top and the rival of its upper end (the largest lower end). On exact readings `hi = lo` and
the term is the pin's. One law, read by the release and by the comparison.

**What it would have done at `m7`.** [agent-inferred before the read below]
- **At the incumbent.** If the swapped stations' gap enclosures overlapped there, as a swap within
  every step size down to `1/2048` suggested, they would lock together and the swap would be gone.
- **At larger step sizes.** They split if the move certifies one above the other, and only then pay
  a split's cost.

**What the main line read** [measured, by the main line, cited; coordinator's relay, October 2]:
- At `m7` the rule releases exactly what the old rule does. In every refinement of all 8 requests,
  no other eligible station's upper end meets the largest certain gap.
- In request 3 the closest pair is at the second freeze: station 2's certain gap `187540480/2^24`
  against station 5's upper end `187166208/2^24`. The order is certified by
  `374272/2^24 = 17·43/2^15`, about 140 cell widths.

So `m7`'s flip is **not** a swap of gaps the readings could not order at the incumbent, and this
rule does not remove it.

**The replay: a true crossing, certain at both ends** [measured, by the main line, cited]. Request
3, second freeze, values over `2^24`:
- At `m7` station 2 locks second: its certain gap exceeds station 5's upper end by `374272`. At the
  successor at `η = 1/2048` station 5 locks second: its certain gap exceeds station 2's upper end
  by `55808` (about 20 cell widths). These are two different certified margins. Each certain gap
  is at most its true gap and each upper end at least, so the true difference `g₂ − g₅` moved by at
  least `374272 + 55808 = 430080 = 2^12·3·5·7`: the true gaps crossed. The certain gaps moved by
  `203264 + 231936 = 435200` (station 2's fell, station 5's rose); the difference, `5120`, is the
  two enclosures' widths. Under linear motion the certified margins cross at `731/840` of the step
  (`374272/430080` reduced); that is where the certified order changes, not where the true gaps
  cross.
- No station is unranked at either state (0 of 64 refinements in each of the 8 requests), so the
  rule above changes nothing at `m7`.
- The freezing order goes from `[0],[2],[4],[5],[6],[7],[3],[1]` to `[0],[5],[7],[6],[4],[3],[2],[1]`.
  The released classes are unchanged (all `3`). The later stations are read with different data
  placed before them, and that is request 3's `+33987/4096`.

So the rule of this section removes only swaps the readings cannot rank. `m7`'s is a crossing of
true gaps, the case `certified_order_needs_crossing` names. Two end states do not show that the
motion is first order. Its location along the step is the carried-cuts record's prediction
([§4b](2026-10-02_THE_STEPS_CANDIDATE_STATES_ARE_THE_CUTS_OF_THE_CARRIED_PATH_AND_THEIR_COUNT_IS_A_WEYL_LAW.md), #211): the replay is consistent with `j_f ≥ j*`. The main
line also finds the rule inert at `m7`: its replay matches the old rule digit for digit.

## 6. Owner and verification

- **Lean.** `lean/Holonics/HNN/ExecutedComparison.lean` §13 (`section Flip`):
  `flip_defeats_first_order`, `flip_curvature_lower`, `no_flip_within_margin`,
  `cell_holds_until_cut`, `cell_moves_at_cut`, `cut_within_cell`. Each depends only on `propext`,
  `Classical.choice` and `Quot.sound` (the audit's `#print axioms`). Checked with
  `lake env lean Holonics/HNN/ExecutedComparison.lean`: no errors, no `sorry`.
- **Lean, §13, the crossing's cost**: `lockFace_sub_abs_le`, `crossing_cost_le`; the same axioms
  only.
- **Lean, §14** (`section CertifiedLock`): `certifiedLock`, `certifiedLock_largest`,
  `leader_locks`, `certifiedLock_exact`, `lone_lock_is_largest`,
  `certified_order_needs_crossing`, `order_solved_locks_no_wrong`; the same axioms only.
- **Rust.** The lock rule's owner, `hnn::prediction`:
  - `uncertified_largest` decides `LockOrder::Gap` from each eligible station's certain gap and
    upper end; it is the only change to the release;
  - test `a_gap_the_readings_do_not_order_below_the_largest_locks_with_it`;
  - the order term's owner, `hnn::executed::order_at`, reads the wrong stations at their upper end
    (`GapEnd`), with test
    `the_order_term_reads_the_wrong_sheets_at_the_upper_end_the_lock_rule_compares`;
  - the trial's `change` field (own less mask) already reads `J`.
- **Owed (#62).** No new obligation from this record. The segment bound `Λ` is a missing owner, not
  an owed proof of an existing statement.
