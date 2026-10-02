# A flip is set by the lock rule's margin, and no law in the chain certifies it before the successor is read

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the statements cited to `HNN/ExecutedComparison` §13; [derived] from the owners'
code where marked; [agent-inferred] where marked. No run. Nothing built in Rust.
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

## 5. Owner and verification

- **Lean.** `lean/Holonics/HNN/ExecutedComparison.lean` §13 (`section Flip`):
  `flip_defeats_first_order`, `flip_curvature_lower`, `no_flip_within_margin`,
  `cell_holds_until_cut`, `cell_moves_at_cut`, `cut_within_cell`. Each depends only on `propext`,
  `Classical.choice` and `Quot.sound` (the audit's `#print axioms`). Checked with
  `lake env lean Holonics/HNN/ExecutedComparison.lean`: no errors, no `sorry`.
- **Rust.** Unchanged. The trial's `change` field (own less mask) already reads `J`.
- **Owed (#62).** No new obligation from this record. The segment bound `Λ` is a missing owner, not
  an owed proof of an existing statement.
