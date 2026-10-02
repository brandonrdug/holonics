# A run closes on a condition, not a length, and the halvings end at the lattice

**Date:** 2026-10-02. **Refs:** #62, #73, #63.
**Grade:** [proved-derived; formal-checked] for the laws (`HNN/ReleaseRun`); [agent-inferred] where
marked; [measured] numbers cite their records. No run. The main line's reads in §6 are owed.
**Revision.** A first draft ended a run at a return to a state it had already met, on a finite set
of states. The deposit clock and the carried Gram advance at every move, so no state repeats and
the set is not finite; that end and its theorems were withdrawn before commit (§1).

## 0. The question

The native chain carries two chosen counts of eight. The constants audit (#150) lists both, and
Astra's review of October 2 called the first a chosen work bound.
- **The run length `W = 8`**: the most moves from an opening state to its close
  ([the endpoint comparison](2026-10-02_THE_RELEASE_GUARD_CERTIFIES_THE_FIXED_MASK_AND_CHARGES_THE_FLIP_OVER_A_WINDOW.md)
  §4.3, `ReleaseExcursion`).
- **The halving count `LADDER_DEPTH = 8`**: the most step sizes a move tries, from its first step
  down to `2^(−7)` of it (`hnn::executed`).

Both now bind. In the main line's diagnostic chain from the opening, with `ρ` held at
`168127/262144`, moves 5 to 12 formed one run that closed only on its last allowed move. Moves 14
to 16 were still an open run at the limit. At `m7` all eight halvings, `1/16` down to `1/2048`,
were refused.

#202 says repayment is necessary and not sufficient. This record asks what the repayment law fixes
in place of each count. Where nothing fixes a count, it says what releasing the count adopts that
the count now refuses. The commitment order and the walls are the derivations thread's subject and
are not taken up here.

## 1. What the close and the move read

**The close reads three quantities.** The run's comparison is `ReleaseExcursion::from_checkpoint`.
Its excursion is unchecked, so `admits` returns every successor (`hnn::executed`,
`ReleaseExcursion::admits`; the range is finite by #202 §5). The close,
`ReleaseExcursion::closes`, is `end.upper < opening.lower − σ`. It reads the opening state's
code-length enclosure, the current state's enclosure and the grain
`σ = decisions · tolerance · ln 2` (`ReleaseExcursion::grain`), which is fixed while the requests
are held. It counts no moves and accumulates nothing along the run. The `(F + σ)/d` bound is a
consequence of the close, not a term of it.

**The move reads the whole continuing state.** `executed_move_guarded` reads the field, the
constitution, the requests, the declared refinement, the bank, the grain, the comparison, the
metric and the unchecked excursion. It reads no seed. The halvings' trial count starts afresh at
every move. The constitution carries two quantities that advance at every adopted deposit
(`hnn::constitution`, module header; atlas `hnn.continuing-state`):
- **the deposit clock `m`**, the count of epochs at the locus's section. Its precision
  `k_m = 2⌊log₂ m⌋ + 1` (`gamma_length`) sets the fine lattice `2^(−L−k_m)ℤ`. It also enters
  the carried coordinate's rounding offset `c = 1/2 + 2^(−k−1)`
  ([the cuts record](2026-10-02_THE_STEPS_CANDIDATE_STATES_ARE_THE_CUTS_OF_THE_CARRIED_PATH_AND_THEIR_COUNT_IS_A_WEYL_LAW.md));
- **the carried Gram `H`**, within one unit of `I + Σ w f fᵀ` over every deposit so far.

Two consequences follow.
- **No state of a run repeats.** The clock strictly advances at each adopted move, so the run's
  continuing states are all distinct, and the states a chain can reach are not finite. A return of
  `(E, ρ)` alone repeats nothing: the move from it reads a later clock and a larger Gram. So there
  is no cycle in the deposition path to end a run.
- **A restart repeats the failed run.** An unclosed run is discarded and the path restarts from its
  opening, which restores the opening's whole `Constitution`, clock and Gram included (#202 §6).
  Nothing outside that state enters a move, so the restarted run passes through the same states and
  fails at the same count again. Under `W = 8`, a restart is not a new attempt: an unclosed run
  stops the chain at its opening. [agent-inferred from the owner's inputs. The diagnostic chain
  never restarted (§6, read 2), so no restart has been observed yet]

## 2. The run: a condition, not a length

#202's `window_closes_iff` says when a run of a given length closes: when its held decreases exceed
its jumps by `σ`. **That condition admits a first close at every length** (`close_at_any_length`).
For every `W` and every `σ ≥ 0`, some path has a positive held decrease at every move and jumps
bounded by `σ + 1`, stays at or above the opening's code length less `σ` through move `W`, and
closes at move `W + 1`. So the repayment law fixes when a run closes, never how many moves the
close takes. Nothing else in the chain's laws fixes a length:
- the moves read a state that never repeats (§1), so no finite count of states bounds a run;
- the run's ends are the **close**, a grain below the opening, and a **refusal**, where no halving
  adopts.

`W = 8` is neither. It is a bound on work.

Two counts are already derived, and neither is an upper end on one run.
- The run needs at least `(F + σ)/d` moves to repay jumps summing to `F` against a per-move
  certified decrease of at most `d` (`window_length_lower`). For `m7`'s jump that is at least 95
  moves, unless a move certifies more than `m7`'s smallest step did (#202 §4.3).
- At most `(f 0 − m)/σ` runs close over the whole path (`grain_windows_bounded`).

**What releasing `W` adopts.** Every run that repays its jumps after more than eight moves. Under
`W = 8` such a run is refused at move eight and, by §1, stops the chain for good. Released, it
continues until it closes or a move is refused. A run that closes within eight moves is unchanged.

[agent-inferred] Nothing bounds the work of a run that never closes, so the chain keeps a declared
bound on moves. It is a resource declaration under the waiting standard: projected before launch,
and an unclosed run at that bound is reported incomplete, never as the law's refusal. Its restart
is never counted as a new attempt.

## 3. The halvings: the lattice already ends them

1. **The code already has a derived end.** `ladder` stops halving when `η · 2u < λ`, where `λ` is
   the source port's lattice unit and `u` is the unit move's largest entry change. That end is the
   lattice's resolution of the move. Below it every entry moves by less than half a lattice unit,
   so its carried coordinate moves by at most one, and only where its remainder lies next to a cut
   (`below_floor_one_coordinate`, from `CarriedCuts.coordinate_moves_lt`). The carried change is
   then set by the remainders, not by the direction. The first step lies within the entry scale,
   `η₀ · 2u ≤ 1` (`ladder_start`), so a halving `k` is tried only with `2^k ≤ 1/λ`
   (`attempted_halvings_le_lattice`). The lattice alone allows at most `⌊log₂(η₀·2u/λ)⌋ + 1`
   step sizes. `LADDER_DEPTH = 8` is a second, tighter count. It binds only where the lattice's end
   lies more than seven halvings below `η₀`, and at `m7` it does (§6).
2. **Halvings between two cuts read one state.** The carried successor changes only at the cuts of
   the carried path
   ([the cuts record](2026-10-02_THE_STEPS_CANDIDATE_STATES_ARE_THE_CUTS_OF_THE_CARRIED_PATH_AND_THEIR_COUNT_IS_A_WEYL_LAW.md)).
   Halvings that fall between the same two cuts read the same carried state and give the same
   verdict. The distinct states the halvings can read are indexed by the cuts below `η₀`; below the
   first cut the carried successor is the incumbent itself.
3. **How deep the adopting halving lies.** #225 proves that with the commitment order fixed and a
   negative slope, some halving adopts (`fixed_order_halving_adopts`). It says nothing of which
   one. With a curvature bound `K` along the move from its slope `d < 0`, so that
   `f η ≤ f 0 + dη + Kη²/2` on `(0, η₀]`:
   - every halving with step at most the **curvature length** `|d|/K` decreases by at least half its
     first-order decrease (`halving_within_curvature`);
   - such a halving exists (`exists_halving_within`) at depth `⌈log₂(η₀K/|d|)⌉`;
   - the first such halving decreases by more than `d²/(4K)` (`least_halving_decrease`). The
     receiver reads that decrease when the enclosures' widths together lie below `d²/(4K)`.
     Otherwise the move lies beneath the grain at every depth.
   - where a commitment crosses a whole turn at `η_c` (#225), the adopting halving must also lie
     below `η_c` (`halving_adopts_before_crossing`). That adds depth `⌈log₂(η₀/η_c)⌉`.
4. **For the kinetic move the count reads the curvature's excess over the receiver's model.** The
   kinetic first step is the Gauss–Newton step `η₀ = 1`, the minimizer of the model whose curvature
   along the move is the receiver's Fisher form, `−d` [proved-standard]. If the comparison's
   curvature is at most `2^m` times the model's, the `m`-th halving lies within the curvature
   length (`gauss_newton_halvings`). Eight step sizes reach curvature up to `2^7 = 128` times the
   receiver's model. [agent-inferred] The excess comes from what the Fisher form leaves out: the
   curvature of the growths `κ = log a` themselves in `E`, the monodromy's second order, and the
   jumps of the released commitments. Where the entry scale
   caps `η₀` below one, fewer halvings are needed.
5. **What no count adopts.** A jump present at every small step refuses every halving (#225,
   `jump_refuses_every_halving`), and no count reaches below it. `m7`'s jump is not of that kind:
   its certified gaps cross at `731/840` of the `1/2048` step under linear motion of the margins
   (§6), so the ninth step size, `1/4096`, lies before it if that motion holds.

**What fixes the count.** The chain reads no curvature bound `K` along a move and no crossing
distance `η_c`. So nothing in its readings derives a depth to replace eight. The lattice's end is
derived, and the code already stops there.

**What releasing it adopts.** Moves whose adoptable steps all lie below `η₀/2^7`, the eighth step
size, and above the lattice's end. These are the moves whose curvature exceeds the receiver's model by more than 128, or whose
nearest whole-turn crossing lies within `η₀/128`. The cost is at most `⌊log₂(η₀·2u/λ)⌋ + 1` step
sizes, each re-reading every request. Steps between two cuts can be skipped, since they read one
state.

## 3b. The entry scale: chosen, and not binding here

The first step is held within the entry scale `½/u` (`ladder_start`), so `n` moves change an entry
of `E` by at most `n/2` (`reach_le_moves`). The scale is chosen, not derived. Adoption never needs
it, since every trial is adopted on the successor's own re-read, and each metric already derives
its own step (Kinetic `η = 1`). It does not bind here: the main line measured that five moves at
`½` reach the refit's largest entry from the opening or from `m6`. Every one of the chain's sixteen
moves points away from the refit (its cosine with the direction to the refit is negative), so the
shortfall is the move's direction, which the derivations thread holds. Releasing the scale would
lengthen the step and leave the Gauss–Newton direction as it is, so it is not a remedy for that
gap.

## 4. Decisions [agent-inferred]

- **Run.** A run ends at its close or at a refusal. Any bound on moves is a resource declaration,
  and an overrun is reported incomplete. The restart is dropped as an attempt: an unclosed run
  stops the chain at its opening, and the receipt says so.
- **Halvings.** The halvings end at the lattice's resolution, which the code already reads, and
  `LADDER_DEPTH` is retired.
- **Entry scale.** Kept as chosen: it does not bind (§3b).

Both changes alter HNN behaviour. They merge only after the main line reads `m7` and the diagnostic
chain under them and campaign 1's held-out read holds.

## 5. What this does not settle

- Whether a released run closes on the diagnostic chain. That is read 5 (§6).
- The curvature bound `K` along a move. It would turn §3.3 into a computed depth. Its derivation from
  the monodromy's second order is owed in #62.
- Whether the carried Gram's growth makes the moves shrink until no lattice coordinate moves, which
  would end every unclosed run in a refusal. The Gram grows along the fed directions only, and the
  first step's entry scale `½/u` rescales the move, so no such end follows from the laws read
  here.

## 6. The main line's reads

Answered (relayed October 2):
1. **`m7`'s refused move.** `η₀ = 1/16` (`KineticEntryScale`). Eight trials ran from `1/16` to
   `1/2048`, so `LADDER_DEPTH`, not the lattice, ended them. `1/16 = power_below(½/u)` puts `u` in
   `(4, 8]`, and the lattice's end lies many halvings lower. At `m7` the certified margins of
   stations 2 and 5 cross at `731/840` of the `1/2048` step under linear motion between the
   incumbent and that trial (the flip record's replay). No law bounds the margins' motion over the
   step, so this is a linear reading, not a certified location of the gap order's change. If it
   holds, a ninth step size, `1/4096`, lands before it; there the order is the incumbent's and
   #225's adoption law applies, provided the decrease clears the enclosures (§3.3).
2. **The diagnostic chain** never restarted and never retraced a state. No move was refused. Every
   move took one trial except moves 5 and 12, which took two. So `W` has not yet refused a run
   there: moves 5 to 12 closed at their eighth move, and moves 14 to 16 were open when the chain's
   move count ended.
3. **Reach.** The largest entry distance from `w16` to the refit's `E` is
   `6458652/2^21 = 3 + 167196/2^21`, inside the sixteen moves' reach of `8`. From the opening or
   `m6` it lies between `2` and `3`, within five moves at `½`. The chain covers about as much
   distance as the refit lies away, but every move points away from it (§3b).

Owed:
4. `m7`'s move read at `1/4096` and below to the lattice's end: which step size adopts, and the
   lattice exponent `L` that sets the end.
5. From the move-13 opening, the run continued to its close or a refusal: which end, at which move.
   It is projected and bounded by the waiting standard before launch, and a run that reaches its
   deadline is reported incomplete.

## 7. Receipts

- `lake env lean Holonics/HNN/ReleaseRun.lean`: no errors, warnings or `sorry`. The audit prints
  `propext`, `Classical.choice` and `Quot.sound` only.
- `bash tools/lean_check.sh Holonics.HNN.ReleaseRun Holonics.HNN`: in the PR's verification.
- No Rust changes.
