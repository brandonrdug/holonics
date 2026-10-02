# A flip is set by the lock rule's margin, and no law in the chain certifies it before the successor is read

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the statements cited to `HNN/ExecutedComparison` §13 and §14; [measured] for the
main line's numbers in §4a; [derived] from the owners'
code where marked; [agent-inferred] where marked. No run here. The lock rule changes in Rust (§5).
Follows [the release guard](2026-10-02_THE_RELEASE_GUARD_CERTIFIES_THE_FIXED_MASK_AND_CHARGES_THE_FLIP_OVER_A_WINDOW.md)
(its §1 holds `m7`'s measurement: at every rung from `η = 1/16` to `1/2048` the own release reads
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
successor is read.** The trial reads it exactly at each rung, and the window of §12 is where it is
paid.

The main line's read (§4a) places `m7`'s flip in the lock rule's ranking of near-tied gaps, which
the rule read on cell ends. §5 gives the rule that locks together every station the readings do not
certify below the largest gap. No move can swap a certified order without the readings crossing.
The rule is forced by the release's own reading of its other decisions.

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

## 3. Whether the move can certify the flip it causes

### 3a. By a first-order bound on the own release: no

- **A flip present at every small step defeats every first-order bound**
  (`flip_defeats_first_order`). If `own η = g η + J` on `(0, δ)` with `J > 0`, `own 0 = g 0` and `g`
  right-continuous, then for every slope `s` and curvature `K` some step has
  `own 0 − η s + K η² < own η`.
- **A flip at a positive `η_c` needs a curvature constant of at least its cost over `η_c²`**
  (`flip_curvature_lower`): `J − η_c (s₁ − s) ≤ K η_c²`. Here `s₁` bounds the continuous part's fall.
  At `m7` the flip is present at `η = 1/2048` on a ladder that starts at `1/16`. So its `η_c` lies
  at or below `1/2048`, and a smooth bound through it would need
  `K ≥ 34038 · 2^10 − 2048 (s₁ − s)` nats per unit step squared, on a comparison whose
  first-order slope the ladder reads at order one. No such constant is in the chain, and none
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
  term on the same margin, the right station's gap against the wrong ones' at `r*`. Descending it
  pushes kind-A margins away from zero at first order. It is still a term to descend, not a
  certificate. Under `Reading::Decisions` it is read only at `r*`, so a kind-A flip at `r₀ < r*` is
  outside it.

**So no law in the chain certifies a flip before the successor is read.** The flip is certified
exactly at the trial, which reads both comparisons. It is paid over a window or refused there.
[agent-inferred] Supplying `Λ` would take a new owner: a segment bound on the root separation of each
read monodromy. Until it exists, a flip-free step can be predicted but not certified.

## 4. What the main line's per-decision read decides

[agent-inferred] The `m7` flip persists at every rung down to `1/2048`. That is what §3a describes
when a margin lies within the summed cell widths (or a tie), or when `μ/|μ′|` is below `1/2048`.
Three readings at the incumbent of `m7`'s first refused move settle which:
1. **The first changed refinement.** `r₀`, its kind (A, B or C), and the stations it re-reads.
2. **The margin at `r₀`.** Its visible value `μ` and the four cell widths. A margin within the widths
   means no step avoids the flip. Above them, the gap covectors at `r₀` give the predicted crossing
   `μ/(−μ′)`.
3. **The cost per station.** `J` per station as `V_j`. If kind A, the `34038/4096` total is the value
   of the correct locks dropped between `r₀` and each station's site.

If it is a kind-A flip within the cell widths, the flip is set by the release's grain and not by the
step. No step size, window length or first-order bound reaches it. What remains is to change the
decision or the grain it is read at, not the guard.

### 4a. The main line's read: a near-tie swap of the lock order (kind C)

[measured, by the main line, cited] At `η = 1/2048`, `m7`'s flip is one decision chain in one
request, and it is of kind C, not the kind A this record expected:
- **Request 3 carries it.** Request 3 rises from `43957/4096` to `77944/4096` (`+33987/4096`). The
  other seven requests fall by `306/4096` in total.
- **The released section is unchanged.** It reads `[3,3,3,3,3,3,3,3]` before and after, wrong at six
  of eight stations: a degenerate release.
- **The lock order changes.** Among near-tied gaps the ranking swaps which station locks first. Six
  stations are read at different partial sections, and three terms' tops flip (stations 3, 6, 7).
- **Per station** (each a lower end over `4096`, good to within `6/4096`): `ℓ` moves
  - station 1 by `+2742`, station 3 by `+6100`, station 4 by `+11986`, station 6 by `+9452`,
    station 7 by `+3815`;
  - station 2 by `−105`, station 0 by `−4`, station 5 by `−2`.
- **Per rung**, as (realized fixed-mask decrease `d`, flip, own less incumbent), each over `4096`:

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
- **The float path's excursions are not flips of this kind.** Its flip part per ten-step window has
  both signs and nets negative, and per term is at most `227/4096`, against `m7`'s about
  `532/4096`. Its rises are continuous: minibatch steps on other requests raise its own read mask.

So the flip sits in the lock rule's ranking of near-tied gaps, which §1 shows is read on cell ends.
§5 takes the rule itself.

## 5. The lock order the readings certify

**The defect.**
- Each eligible station's true gap `a_top − max_(x≠top) a_x` is enclosed by its **certain gap**
  `lo = L_top − max U` (what the release reads) and its **reach** `hi = U_top − max L`.
- The rule as it stood locked only the strictly largest certain gap.
- So two stations whose gap enclosures overlap were ordered by where their cells' cuts fell, not by
  their readings. A move too small to change any reading's order still swapped them, as at `m7`.

**The rule, in the lock rule's owner, with no second rule.** A station locks when no station's
certain gap exceeds its reach: every station the readings do not certify below the largest locks
with it. On exact readings (reach = certain gap) this is the largest gap with its ties, the rule as
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

**Forced or chosen.** [derived] Forced by the release's own reading of its other decisions:
- A top exceeds its rivals only when its `L` exceeds every rival's `U`, and a station locks only
  when its `L` exceeds one. Both are certified orderings of enclosures.
- An ordering the enclosures do not certify is read plural: "no positive gap is a plural reading",
  "ties lock together".
- The gap ranking was the one decision that compared bare cell ends as if they were readings.
- Reading it the same way leaves nothing to choose. The comparison `≥` (reach meeting the largest)
  keeps a possible true tie together, as the exact rule does. The cells are the receiver's declared
  grain.

[agent-inferred] The one alternative, refining the cells until near ties order, changes the
receiver's grain, which the release does not own. So it is refused.

**What it would have done at `m7`.** [agent-inferred; to be measured by the main line]
- **At the incumbent.** If the swapped stations' gap enclosures overlap there, as a swap within
  every rung down to `1/2048` indicates, they lock together. The incumbent's own release then
  changes too: different sections and a different incumbent comparison.
- **At `η = 1/2048`.** Their true gaps move by about `η` times their slope. They stay uncertified
  unless that motion exceeds the overlap, and then both rule outputs keep them together. The swap,
  and with it request 3's `+33987/4096`, is gone; the rung adopts on the fixed mask's decrease.
- **At larger rungs.** They split if the move certifies one above the other, and only then pay a
  split's cost.
- **To measure.** Re-run `m7`'s incumbent and its first refused move on this rule. Read:
  - the two stations' certain gaps and reaches at the incumbent;
  - the own less incumbent per rung;
  - whether any rung still flips.

## 6. Owner and verification

- **Lean.** `lean/Holonics/HNN/ExecutedComparison.lean` §13 (`section Flip`):
  `flip_defeats_first_order`, `flip_curvature_lower`, `no_flip_within_margin`,
  `cell_holds_until_cut`, `cell_moves_at_cut`, `cut_within_cell`. Each depends only on `propext`,
  `Classical.choice` and `Quot.sound` (the audit's `#print axioms`). Checked with
  `lake env lean Holonics/HNN/ExecutedComparison.lean`: no errors, no `sorry`.
- **Lean, §14** (`section CertifiedLock`): `certifiedLock`, `certifiedLock_largest`,
  `leader_locks`, `certifiedLock_exact`, `lone_lock_is_largest`,
  `certified_order_needs_crossing`; the same axioms only.
- **Rust.** The lock rule's owner, `hnn::prediction`:
  - `uncertified_largest` decides `LockOrder::Gap` from each eligible station's certain gap and
    reach; it is the only change to the release;
  - test `a_gap_the_readings_do_not_order_below_the_largest_locks_with_it`;
  - the trial's `change` field (own less mask) already reads `J`.
- **Owed (#62).** No new obligation from this record. The segment bound `Λ` is a missing owner, not
  an owed proof of an existing statement.
