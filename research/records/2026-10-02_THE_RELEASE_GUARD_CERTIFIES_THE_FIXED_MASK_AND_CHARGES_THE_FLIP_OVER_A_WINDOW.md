# The release guard certifies the fixed mask and charges the flip over a window

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the laws (`HNN/ExecutedComparison` §12); [measured] numbers cited from their
records; [agent-inferred] where marked. No run.

## 1. What the measurements ask of the guard

- **The refit's ablation located no optimizer ingredient.** Plain gradient steps reach 57 whole
  sections on two seeds, as many as the scaled arms
  ([the ablation](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md) §2).
- **That path's own comparison rises above its opening** (the same record, §3). Seed 202 opens at
  `161209/100000` nats per decision and exceeds it at step 30 by `1471/1000000`. Seed 303 opens at `402113/250000`
  and exceeds it at step 60 by `1311/10000` (the receipts' printed values). Its excursions above the running minimum last 20 to 60
  steps and peak at up to `481/1000` per decision. Each ends below the earlier minimum.
- **The native chain stops at the guard** (the kinetic move's receipts, `m5` to `m7`). Every refused
  rung is `OwnNotBelow`. At `m7` all eight rungs, from `η = 1/16` down to `1/2048`, are refused. At
  `1/2048` the fixed mask falls from `337896/4096` to `337537/4096`, while the own release reads
  `371575/4096`: `34038/4096` above the fixed mask at the same `E`, even at the smallest rung.

So the guard as it stood refuses the path that reaches the sections, and it refuses the native move
at a discontinuity that no step size removes. Two questions follow: what the guard should compare,
and how a rise is paid for.

## 2. What the guard compares

1. **The first-order certificate speaks to the fixed mask.** The move's slope is certified on the
   incumbent's mask, the incumbent's decisions kept: Danskin's bound over the members
   (`lockFace_first_order`, `sum_upper_dini_descends`) and the disjoint enclosures
   (`disjoint_enclosures_decrease`). Along the move that comparison is continuous, and a certified
   slope makes it fall for small enough steps.
2. **The own release is the fixed mask plus a flip.** Let `f k` be the own release at the `k`-th
   adopted state and `m k` the incumbent's fixed mask read at the successor. At the incumbent the two
   agree. So `f (k+1) − f k = (m k − f k) + (f (k+1) − m k)` (`own_telescopes`). The first term is
   the fixed mask's change. The second is the **flip**: the successor's own decisions read against
   the incumbent's on the same `E`. The trial receipt's `change` (the own reading less the mask's)
   already encloses it.
3. **A flip can be either sign.** The release's decisions come from its lock rule (a nonempty set of
   the largest-gap eligible stations locks), not from the comparison. So the own release is not the
   least of the masks. A successor's decisions can read worse than the incumbent's on the same `E`,
   which is `m7`'s `+34038/4096`.
4. **The flip is not certifiable at first order.** It is a jump at a cell boundary. No slope bounds
   it, and no smaller rung removes it once the boundary lies inside every rung, as at `m7`.
5. **The comparison that counts is still the own release.** A comparison is read through the
   contemporary constitution and returns its residual (the retention law). The own release is what
   the machine releases, and the next move's incumbent reads it. So the guard cannot drop it. It can
   only stop asking a single step to certify what a step cannot certify.
6. **When a flip is re-read.** Exactly once, at the next move. That move's incumbent is the
   successor's own release (`incumbent`), so its fixed mask holds the flipped decisions and its own
   certificate starts from them. Nothing records a flip beyond that; the window below holds one
   comparison, its checkpoint's.

**So each step certifies the fixed mask's fall (`NotBelow`, unchanged), and the flips are charged to
a window**: they are paid when the window's certified fixed-mask decreases exceed its net flips.
[agent-inferred] The exterior float path is this law with no window: each step is a gradient step of
the mask at the current state, accepted whatever the flip.

## 3. The law and what it certifies

From a checkpoint `t n`, every own comparison until the next checkpoint stays below the
checkpoint's plus a height `h ≥ 0`. The next checkpoint, at most `W` adopted moves on, lies below
the checkpoint's less a certified decrease `σ n ≥ 0`. A window that does not close returns to its
checkpoint.
- **One step and no height is the former guard** (`checkpoint_one_iff`). The check on enclosures'
  ends is sound (`excursion_enclosure`).
- **A window closes exactly when its fixed-mask decreases exceed its flips by `σ`**
  (`window_closes_iff`).
- **The checkpoints descend by the certified decreases** (`checkpoint_descends`): `f (t n) ≤ f 0 −
  Σ_(b<n) σ b`. **Nothing exceeds the opening by more than `h`** (`excursion_le_start`).
- **The decreases are summable** (`checkpoints_sum_le`, `large_windows_card`): below a floor `m`,
  `Σ σ ≤ f 0 − m`, and at most `(f 0 − m)/ε` windows certify `ε` or more.
- **The schedule's condition** (`schedule_frequently_small`): with `σ n = η n · q n` and a divergent
  step sum, the windows' least slope `q` falls below every `ε` in windows beyond every point. **None
  of the chain's step schedules is summable.**
  - The ladder's adopted steps each move at least one lattice coordinate, `η ≥ u/(2U)`
    (`floor_steps_diverge`).
  - The normal law's carried Gram grows at most linearly, a harmonic lower bound on its step.
  - The contact freeze's `1/m²` is the fine lattice's cell, not a step size.
  - The dyadic rungs reset each move.

  With a positive margin under the floor the slopes themselves are summable
  (`floor_large_slopes_card`). (The lattice-floor stall `K u²/32` is on its own parked branch; the
  `m5`–`m7` refusals are all `OwnNotBelow`, so it is not the cause.)

## 4. The parameters, from the chain's laws

The float path's numbers check these; they do not set them.

1. **The height `h`: derived, and not a parameter inside a window.** The entry bound holds every
   adopted `E` within `2^3` an entry. With the readings bounded away from zero there
   ([agent-inferred]; §5's review), the comparison is bounded on the adopted states, between a floor
   `m` and some `B`. A bounded comparison satisfies every window's excursion with `h = B − m`
   (`excursion_of_bounded`). So no per-step check of the own release is owed inside a window, and
   the owner's window runs with the height unchecked (`ReleaseExcursion::from_checkpoint`). The
   largest flip the lock rule allows on one move is bounded by the same range. A finite `h` below
   `B − m` would only end futile windows sooner; that is the window's length's job (3).
2. **The decrease `σ`: derived from the receiver's grain.** A decrease below the grain is not a
   reading: the comparison is read at `tolerance` bits per decision, so a window closes by at least
   one grain over the batch, `σ = decisions · tolerance · ln 2` nats (`ReleaseExcursion::grain`, at
   the upper end of `ln 2`'s enclosure). Then at most `(f 0 − m)/σ` windows close
   (`grain_windows_bounded`): the chain releases at the grain instead of running on. The tolerance is
   the declared `1/16` bit, the root of every scale (PR #150); under #150's derived grain `1/L(N)`
   it would refine with the readings.
3. **The length `W`: bounded below by the laws, its upper end a choice.**
   - **At least two moves.** A window of one closes only when the move's own fixed-mask decrease
     covers its flip (`one_move_closes_iff`). That decrease was certified on the incumbent's mask,
     before the flip was read. The flip is re-read once, at the next move, so only a later move can
     answer it.
   - **At least `(F + σ)/d` moves** for flips summing to `F` against a per-move certified decrease
     of at most `d` (`window_length_lower`). So two is a lower bound, not the length. At `m7`,
     `F = 34038/4096`. If no move certifies more than the `359/4096` that `m7`'s smallest rung did,
     the flip needs at least 95 moves. A move that certifies more shortens that in proportion.
   - **The upper end is the chain's choice.** It bounds the moves a window that does not close
     spends before returning to its checkpoint. No law of the chain fixes it.

[agent-inferred] The checks owed from the main line:
- the float path's excursions per decision against the grain;
- its 20 to 60 steps against `(F + σ)/d`, once steps convert to moves;
- `m7`'s per-rung certified decreases, which give `d`.

Until then the owner runs the monotone guard, which is the former rule.

## 5. The owner

`hnn::executed::ReleaseExcursion` (a held checkpoint, `None` for the incumbent, and an optional
`height`) replaces the `OwnNotBelow` rule in the ladder:
- `admits`: `own.upper < checkpoint.lower + height`, every successor when the height is unchecked.
- `grain`: `σ`, one receiver grain over the batch.
- `closes`: `end.upper < checkpoint.lower − σ`.

`executed_move_in` passes `ReleaseExcursion::monotone()`, exactly the former rule.
`executed_move_guarded` takes the chain's excursion. `ReleaseExcursion::from_checkpoint` opens a
window at a held checkpoint. The chain holds the checkpoint, counts the window and returns to the
checkpoint when a window does not close. The fixed mask's `NotBelow` is unchanged.

Review (#202): the fixed mask's `NotBelow` is tested before the excursion on every rung, so no
window skips it. The return restores the checkpoint's whole `Constitution`, held by the chain as one
state (not a tape), and every successor the failed window adopted is discarded: §12's
`CheckpointGuard` indexes adopted states only, which presumes exactly that. `ReleaseExcursion`
holds only the checkpoint's comparison, which is all the step's guard and the close read; no chain
owner runs windows yet. The unchecked height is sound whatever its value, because only the chain
reads a window's states and it releases only a closed window's checkpoint. Its finiteness, §4's
`B − m`, is [agent-inferred]: the entry bound bounds `E`, but a bounded comparison also needs the
readings bounded away from zero on the admitted states, which no guard states, so
`excursion_of_bounded`'s hypothesis is not discharged. A held negative height states no guard (the
checkpoint itself would breach its excursion) and a negative `σ` lets a checkpoint rise, so both
are refused, typed: `executed_move_guarded` refuses `HnnError::ExcursionHeight` before any reading,
and `closes` returns `HnnError::WindowDecrease`. `σ` is in the comparison's units: the comparison
is the batch's total in nats (its logarithms are `ln` enclosures), and one grain of `tolerance`
bits per decision is `decisions · tolerance · ln 2` nats.

## 6. Verification

- `lake build Holonics.HNN.ExecutedComparison`: no `sorry`; the audit prints `propext`,
  `Classical.choice` and `Quot.sound` only.
- `cargo check --workspace --all-targets` is clean.
- `hnn::tests::executed::the_monotone_excursion_is_the_strict_decrease_and_a_height_admits_a_bounded_rise`
  passes. It checks the monotone guard against the former rule on seven enclosures, a held
  checkpoint's height in both directions, and the window's close in both directions.
