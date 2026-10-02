# The released code length is compared between two endpoint states, and the lattice bounds the states between

**Date.** October 2; restated in physical terms the same day (Brandon: "abstract the cycles and
logic with physics … I don't like 'window' at all either when you mean boundary endpoints"). The
file keeps its first name so that links hold. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62.
**Grade.** [proved-derived; formal-checked] for the laws (`HNN/ExecutedComparison` §12,
`HNN/Floquet` §Floor); [measured] numbers cited from their records; [agent-inferred] where marked.
No run. Code identifiers (`OwnNotBelow`, `ReleaseExcursion`, `CheckpointGuard`, `window_closes_iff`)
keep their first names until a later pass renames them; the prose below does not use them as
concepts.

## 0. The physical statement

Every term names a quantity or a process of the receiving bank.

- **The released code length** `f` is the comparison: the targets' code length in nats, read
  through the release's own commitments. `k_B T · f` is a free energy against the receiver's
  equilibrium; `f` itself is dimensionless.
- **A commitment** is a ring's all-or-nothing lock on its dominant sheet: the zero-temperature limit
  of the lock's shares ([the flip record](2026-10-02_A_FLIP_IS_SET_BY_THE_LOCK_RULES_MARGIN_AND_NO_LAW_IN_THE_CHAIN_CERTIFIES_IT_BEFORE_THE_SUCCESSOR_IS_READ.md) §0).
- **A step** is one deposition: the constitution `E` moves to a successor.
- **The held-commitment code length** `m` is the same code length at the successor with the
  incumbent's commitments held.
- **The jump** (the flip) is `f − m` at the successor: the change in code length where a ring's
  commitment switches. A commitment is all or nothing, so the code length is discontinuous there.
  The size of the jump is set by which data are placed beside which, not by how far `E` moved.

**What is compared, between which two states.** The released code length at the two endpoint
states of an interval of the deposition path: the opening state and the closing state, at most `W`
steps later. The closing state must lie below the opening by `σ ≥ 0`, at least one receiver grain.
A grain is the smallest code-length difference the receiver resolves.

**Why the states between are free.** Each step certifies the fall of the held-commitment code
length; that part is continuous in the step. The jump is not continuous and no step's certificate
reaches it. It is first read when the successor becomes the next step's incumbent, so only a later
step can repay it. Requiring every intermediate state to lower the code length would refuse every
path whose first jump is positive, whatever follows. The measured paths below are such paths.

**What bounds them.** The range of the code length over the admitted states, `h = B − m`. That
range is finite only because a target's reading has a floor: §5 proves the floor from the lattice
and says what happens as a reading falls toward zero.

**What has no physical statement.** An interval that does not close is discarded and the path
restarts from its opening state. No process of the rings undoes a deposition. This is a selection
among paths made by the receiver, not an evolution of the bank, and it is stated as that.

The discontinuity of a decision where two rings' gaps cannot be told apart at the readings'
resolution, and why such rings commit together, are the flip record's subject (§0 and §5 there).

## 1. What the measurements ask of the comparison

- **The refit's ablation located no optimizer ingredient.** Plain gradient steps reach 57 whole
  sections on two seeds, as many as the scaled arms
  ([the ablation](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md) §2).
- **That path's own code length rises above its opening** (the same record, §3). Seed 202 opens at
  `161209/100000` nats per decision and exceeds it at step 30 by `1471/1000000`. Seed 303 opens at
  `402113/250000` and exceeds it at step 60 by `1311/10000` (the receipts' printed values). Its rises
  above the running minimum last 20 to 60 steps and peak at up to `481/1000` per decision. Each ends
  below the earlier minimum.
- **The native chain stops where each step must lower the released code length** (the kinetic
  move's receipts, `m5` to `m7`). Every refused step size is `OwnNotBelow`. At `m7` all eight, from
  `η = 1/16` down to `1/2048`, are refused. At `1/2048` the held-commitment code length falls from
  `337896/4096` to `337537/4096`, while the released one reads `371575/4096`: `34038/4096` above,
  at the same `E`, even at the smallest step.

So strict descent at every step refuses the path that reaches the sections, and it refuses the
native step at a discontinuity that no step size removes. Two questions follow: which two states
are compared, and how a rise is repaid.

## 2. The two parts of a step's change

1. **The first-order certificate speaks to the held commitments.** The step's slope is certified
   with the incumbent's commitments held: Danskin's bound over the members (`lockFace_first_order`,
   `sum_upper_dini_descends`) and the disjoint enclosures (`disjoint_enclosures_decrease`). Along
   the step that code length is continuous, and a certified slope makes it fall for small enough
   steps.
2. **The released code length is the held one plus a jump.** Let `f k` be the released code length
   at the `k`-th admitted state and `m k` the incumbent's held-commitment code length at the
   successor. At the incumbent the two agree, so
   `f (k+1) − f k = (m k − f k) + (f (k+1) − m k)` (`own_telescopes`). The first term is the held
   change; the second is the jump. The trial receipt's `change` (the released reading less the
   held one) already encloses it.
3. **A jump can be either sign.** The commitments come from the lock rule (the rings the readings
   cannot rank below the leader commit together), not from minimizing the code length. So the
   released code length is not the least over commitments, and a successor's commitments can read
   worse than the incumbent's on the same `E`: `m7`'s `+34038/4096`.
4. **The jump is not certifiable at first order.** It sits on the boundary of a commitment cell. No
   slope bounds it, and no smaller step removes it once the boundary lies inside every step, as at
   `m7`.
5. **The quantity compared is still the released code length.** A comparison is read through the
   contemporary constitution and returns its residual (the retention law). The released code length
   is what the machine releases, and the next step's incumbent reads it. The comparison keeps it and
   stops asking one step to certify what a step cannot certify.
6. **When a jump is read.** Exactly once, at the next step, whose incumbent is the successor's own
   release. Its held commitments are the switched ones, and its certificate starts from them.
   Nothing records a jump beyond that; the interval holds one code length, its opening state's.

[agent-inferred] The exterior float path is this law with no endpoint condition: each step is a
gradient step of the held-commitment code length at the current state, accepted whatever the jump.

## 3. The law and what it certifies

From an opening state `t n`, every released code length until the next opening state stays below
the opening's plus `h ≥ 0`. The next opening state, at most `W` steps on, lies below the opening's
less a certified decrease `σ n ≥ 0`.
- **One step and no excursion is strict descent** (`checkpoint_one_iff`), the rule the chain kept
  before. The comparison on enclosures' ends is sound (`excursion_enclosure`).
- **An interval closes exactly when its held-commitment decreases exceed its jumps by `σ`**
  (`window_closes_iff`).
- **The opening states descend by the certified decreases** (`checkpoint_descends`):
  `f (t n) ≤ f 0 − Σ_(b<n) σ b`. **Nothing exceeds the first opening by more than `h`**
  (`excursion_le_start`).
- **The decreases are summable** (`checkpoints_sum_le`, `large_windows_card`): below a floor `m`,
  `Σ σ ≤ f 0 − m`, and at most `(f 0 − m)/ε` intervals certify `ε` or more.
- **The schedule's condition** (`schedule_frequently_small`): with `σ n = η n · q n` and a divergent
  step sum, the intervals' least slope `q` falls below every `ε` in intervals beyond every point.
  **None of the chain's step schedules is summable.**
  - The descent's admitted steps each move at least one lattice coordinate, `η ≥ u/(2U)`
    (`floor_steps_diverge`).
  - The normal law's carried Gram grows at most linearly, a harmonic lower bound on its step.
  - The contact freeze's `1/m²` is the fine lattice's cell, not a step size.
  - The dyadic step sizes reset each step.

  With a positive margin under the floor the slopes themselves are summable
  (`floor_large_slopes_card`). (The stall at the lattice's step, `K u²/32`, is on its own parked
  branch; the `m5`–`m7` refusals are all `OwnNotBelow`, so it is not the cause.)

## 4. The parameters, from the chain's laws

The float path's numbers check these; they do not set them.

1. **The excursion `h`: the code length's range, not a parameter of an interval.** If every
   admitted code length lies in `[m, B]`, every interval's excursion holds with `h = B − m`
   (`excursion_of_bounded`). So no per-step comparison is owed inside an interval, and the owner
   runs the interval with the excursion unchecked (`ReleaseExcursion::from_checkpoint`). The largest
   jump the lock rule allows on one step lies in the same range. A finite `h` below `B − m` would
   only end futile intervals sooner, which is the length's job (3). Why `B` is finite is §5.
2. **The decrease `σ`: one receiver grain.** A decrease below the grain is not a reading: the code
   length is read at `tolerance` bits per decision, so an interval closes by at least one grain over
   the batch, `σ = decisions · tolerance · ln 2` nats (`ReleaseExcursion::grain`, at the upper end
   of `ln 2`'s enclosure). Then at most `(f 0 − m)/σ` intervals close (`grain_windows_bounded`): the
   path releases at the grain instead of running on. The tolerance is the declared `1/16` bit, the
   root of every scale (PR #150); under #150's derived grain `1/L(N)` it would refine with the
   readings.
3. **The length `W`: bounded below by the laws, its upper end a choice.**
   - **At least two steps.** An interval of one closes only when the step's own held decrease
     covers its jump (`one_move_closes_iff`). That decrease was certified before the jump was read,
     and the jump is read once, at the next step, so only a later step can repay it.
   - **At least `(F + σ)/d` steps** for jumps summing to `F` against a per-step certified decrease
     of at most `d` (`window_length_lower`). At `m7`, `F = 34038/4096`. If no step certifies more
     than the `359/4096` that `m7`'s smallest step did, the jump needs at least 95 steps. A step
     that certifies more shortens that in proportion.
   - **The upper end is the chain's choice.** It bounds the steps an interval that does not close
     spends before the path restarts from its opening. No law of the chain fixes it.

## 5. The readings' floor, and a reading that falls toward zero

The review of #202 left one hypothesis undischarged: the entry bound holds every admitted `E`
within `2^3` an entry, but that alone does not bound the code length. This section settles it.

1. **Without a floor the code length is unbounded.** A target's term is
   `ℓ = log((1 + a + r)/a)`, with `a` the target's reading (its Floquet multiplier per pump period)
   and `r` its rivals'. For every `B` a positive reading has `ℓ > B` (`lockFace_unbounded`). The
   entry bound bounds `r` from above but does not keep `a` from zero. So the entry bound alone
   supplies no `h`.
2. **With a floor it is bounded.** With the target's reading at least `ρ₀ > 0` and its rivals at
   most `R`, `ℓ ≤ log(1 + (1 + R)/ρ₀)` (`lockFace_le_of_floor`). This is the condition, stated in
   the theorem.
3. **The lattice supplies the floor.** The monodromy over one pump period is `M = N/Δ`, with `N` an
   integer matrix and `Δ` the product of the period's tick denominators (`turn_monodromy`). If `N`
   is invertible, `|det N| ≥ 1`, and `det N` is the product of `N`'s multipliers, so some
   multiplier has modulus at least one: `ρ(M) ≥ 1/Δ` (`HNN/Floquet.integer_monodromy_floor`). If
   `N` is singular but not nilpotent, its lowest nonzero characteristic coefficient is a nonzero
   integer and the product of the nonzero multipliers, so the same floor holds [derived; its Lean
   statement is owed in #62]. A nilpotent `N` has every multiplier zero.
4. **So a reading does not fall continuously toward zero.** On the lattice a ring's growth is
   either zero or at least `1/Δ`. Physically, a growth of zero means the ring's motion vanishes
   exactly after finitely many periods (`N^n = 0`); there is no slow decay below `1/Δ`. The read
   enclosure's lower end is at least `(1 − 2^(−g))/Δ` at the reading's grain `g`, and the lock
   face's upper end uses that lower end, so the floor binds the enclosure, not only the true value.
5. **What happens to the states inside an interval.** A state whose target reading is zero has an
   infinite code length: the receiver gives the observed outcome no share. Its lock face is refused
   (`HnnError::NonpositiveDeclaration`, surfaced as `TrialRefusal::Unsupported`), so it is never
   admitted and no interval contains it. Every admitted state's target term is then at most
   `log(1 + (1 + R)Δ/(1 − 2^(−g)))`. The bound grows with `log Δ`, the lattice's bits over one
   period: a finer lattice allows a smaller nonzero reading and a larger finite rise.
6. **A defect the floor exposed, fixed.** On a nilpotent `N` the growth reading halved its bracket
   toward zero without end, since no positive radius is ever reached. `growth_of` now returns the
   floor's cell `[0, 1/Δ)` there without bisecting (`hnn::tests::executed::a_reading_is_zero_or_past_the_lattices_floor`).
   Behaviour changes only on a nilpotent monodromy, which before this fix did not return.

[agent-inferred] Two conditions remain without a Lean statement. The rivals' bound `R`: each
multiplier's modulus is at most the monodromy's norm, a product of the period's ticks whose entries
the entry bound bounds. A floor uniform over an interval's states: `Δ` varies with `E`, and it is
bounded across a path when `E`'s entries stay on the constitution's lattice and the source's
amplitudes are fixed, which the descent's steps keep. Both are carried to #62.

## 6. The owner

`hnn::executed::ReleaseExcursion` (a held opening state, `None` for the incumbent, and an optional
excursion) replaces the `OwnNotBelow` rule in the descent:
- `admits`: `own.upper < opening.lower + height`, every successor when the excursion is unchecked.
- `grain`: `σ`, one receiver grain over the batch.
- `closes`: `end.upper < opening.lower − σ`.

`executed_move_in` passes `ReleaseExcursion::monotone()`, exactly strict descent.
`executed_move_guarded` takes the chain's interval. `ReleaseExcursion::from_checkpoint` opens an
interval at a held opening state. The chain holds the opening state, counts the steps and restarts
from the opening when an interval does not close. The held-commitment `NotBelow` is unchanged.

Review (#202): the held-commitment `NotBelow` is tested before the excursion at every step size, so
no interval skips it. The restart restores the opening state's whole `Constitution`, held by the
chain as one state (not a tape), and every successor the failed interval admitted is discarded:
§12's `CheckpointGuard` indexes admitted states only, which presumes exactly that. The owner holds
only the opening state's code length, which is all the step's comparison and the closing read need;
no chain owner runs intervals yet. The unchecked excursion is sound whatever its value, because only
the chain reads an interval's states and it releases only a closed interval's opening state. Its
finiteness is §5. A negative excursion states no condition (the opening state would breach its own)
and a negative `σ` lets an opening state rise, so both are refused, typed:
`executed_move_guarded` refuses `HnnError::ExcursionHeight` before any reading, and `closes`
returns `HnnError::WindowDecrease`. `σ` is in the code length's units: the comparison is the
batch's total in nats (its logarithms are `ln` enclosures), and one grain of `tolerance` bits per
decision is `decisions · tolerance · ln 2` nats.

## 7. Verification

- `lake build Holonics.HNN.ExecutedComparison Holonics.HNN.Floquet`: no `sorry`; the audit prints
  `propext`, `Classical.choice` and `Quot.sound` only.
- `cargo check --workspace --all-targets` is clean.
- `hnn::tests::executed::the_monotone_excursion_is_the_strict_decrease_and_a_height_admits_a_bounded_rise`
  checks strict descent against the former rule on seven enclosures, a held opening state's
  excursion in both directions, and the interval's close in both directions.
- `hnn::tests::executed::a_reading_is_zero_or_past_the_lattices_floor` checks the nilpotent cell
  `[0, 1/4)` and a reading at the floor `1/4` within the grain.
